// The clang-tidy plugin of cplusp. See docs/policy.md.
//
// One generic check, driven by the policy file.
// The gate writes each `matcher` entry of a rule as an option of the check, named `{rule_id}/{n}`.
// The check compiles the pattern and reports every match with the rule id as its message.
// The Rust side turns the rule id into the message for the bot.
//
// Nine hand-written checks, for the rules that a pattern cannot say. The gate maps a finding to its rule by
// the name of the check, so their messages are short and plain. The sample pair of each rule is the evidence.

#include "ClangTidyCheck.h"
#include "ClangTidyModule.h"
#include "ClangTidyModuleRegistry.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/Dynamic/Diagnostics.h"
#include "clang/ASTMatchers/Dynamic/Parser.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/APFloat.h"
#include "clang/Lex/Lexer.h"

#include <algorithm>
#include <initializer_list>
#include <optional>
#include <string>
#include <vector>

using namespace clang;
using namespace clang::ast_matchers;
using clang::tidy::ClangTidyCheck;
using clang::tidy::ClangTidyCheckFactories;
using clang::tidy::ClangTidyContext;
using clang::tidy::ClangTidyModule;

namespace {

// The patterns of the policy run on the full tree. clang-tidy 18 gives a check no traversal kind
// unless it overrides getCheckTraversalKind, so a pattern sees implicit nodes. The `sign_compare`
// pattern relies on that: it matches the cast the compiler adds. The hand-written checks below
// override it and read the tree as spelled in the source.
class MatcherCheck : public ClangTidyCheck {
public:
  // The base class keeps the context private, so the check keeps its own pointer.
  MatcherCheck(StringRef Name, ClangTidyContext *Context) : ClangTidyCheck(Name, Context), Ctx(Context) {}

  void registerMatchers(MatchFinder *Finder) override {
    // Every option of this check is a pattern. The options of other checks do not start with this prefix.
    const std::string Prefix = (getID() + ".").str();
    for (const auto &Option : Ctx->getOptions().CheckOptions) {
      StringRef Key = Option.getKey();
      if (!Key.consume_front(Prefix))
        continue;
      // The key is `{rule_id}/{n}`. A rule id has no `/`, so the last one ends the id.
      StringRef Rule = Key.rsplit('/').first;
      Rules.insert(Rule);
      if (auto Why = addPattern(Finder, Rule, Option.getValue().Value))
        configurationDiag("rule %0 has an invalid matcher: %1") << Rule << *Why;
    }
  }

  void check(const MatchFinder::MatchResult &Result) override {
    // Each pattern is bound to its rule id, so the bound nodes of one match name the rule.
    // A pattern may bind other nodes under its own names. Those are not findings.
    for (const auto &Bound : Result.Nodes.getMap()) {
      if (!Rules.contains(Bound.first))
        continue;
      SourceLocation Loc = Bound.second.getSourceRange().getBegin();
      if (Loc.isInvalid())
        continue;
      // A node from a macro is reported where the macro is used. clang-tidy drops a finding
      // inside a macro of a system header, and `setjmp` is such a macro.
      diag(Result.SourceManager->getFileLoc(Loc), "%0") << Bound.first;
    }
  }

private:
  ClangTidyContext *Ctx;
  // The rule ids read from the options.
  llvm::StringSet<> Rules;

  // Compile one pattern and add it to the finder. Returns the reason when it cannot.
  std::optional<std::string> addPattern(MatchFinder *Finder, StringRef Rule, StringRef Pattern) {
    dynamic::Diagnostics Error;
    StringRef Code = Pattern;
    std::optional<internal::DynTypedMatcher> Parsed = dynamic::Parser::parseMatcherExpression(Code, &Error);
    if (!Parsed)
      return Error.toStringFull();
    std::optional<internal::DynTypedMatcher> Bound = Parsed->tryBind(Rule);
    if (!Bound)
      return "it is not a node matcher, so it has nothing to bind. Start it with a matcher such as varDecl.";
    if (!Finder->addDynamicMatcher(*Bound, this))
      return "it is not a matcher for a declaration, statement, type or similar node.";
    return std::nullopt;
  }
};

// ------------------------------------------------------------ hand-written checks

// These checks read what the author wrote. The traversal skips implicit nodes, such as the begin and end calls
// of a range-for, and template instantiations. A matcher also looks through implicit casts and temporaries.
class SpelledCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  std::optional<TraversalKind> getCheckTraversalKind() const override { return TK_IgnoreUnlessSpelledInSource; }
};

AST_MATCHER(FieldDecl, isMutableField) { return Node.isMutable(); }

// The declaration is in namespace std, however deep. A member of a std class counts, and so does std::ranges.
bool inStdNamespace(const Decl *Declaration) {
  for (const DeclContext *Context = Declaration->getDeclContext(); Context; Context = Context->getParent())
    if (Context->isStdNamespace())
      return true;
  return false;
}

AST_MATCHER(Decl, isInStd) { return inStdNamespace(&Node); }

// A call of a std function, or a construction of a std class. An operator other than () is no call here:
// `v.rbegin() + 2` is arithmetic, and the operator is a member of std::reverse_iterator.
auto stdCall() {
  return expr(anyOf(callExpr(callee(functionDecl(isInStd())), unless(cxxOperatorCallExpr(unless(hasOverloadedOperatorName("()"))))),
                    cxxConstructExpr(hasDeclaration(isInStd()))));
}

// cplusp-mutable: every field declared `mutable`.
class MutableCheck : public SpelledCheck {
public:
  using SpelledCheck::SpelledCheck;
  void registerMatchers(MatchFinder *Finder) override { Finder->addMatcher(fieldDecl(isMutableField()).bind("field"), this); }
  void check(const MatchFinder::MatchResult &Result) override {
    diag(Result.Nodes.getNodeAs<FieldDecl>("field")->getLocation(), "field is mutable");
  }
};

// A pure interface has no field, and every function it declares is pure virtual. Its destructor may be declared
// if it is virtual. Its own bases must be pure interfaces too, so the whole class is judged.
// A function template is a function it declares, and it is never pure.
bool isPureInterface(const CXXRecordDecl *Record) {
  Record = Record->getDefinition();
  if (!Record || !Record->field_empty())
    return false;
  for (const Decl *Member : Record->decls()) {
    const auto *Method = dyn_cast_or_null<CXXMethodDecl>(Member->getAsFunction());
    if (Method && !Method->isImplicit() && !Method->isPureVirtual() && !(isa<CXXDestructorDecl>(Method) && Method->isVirtual()))
      return false;
  }
  // ponytail: a dependent base has no record yet, so it counts as no base. A template's instantiations are not
  // visited, so `template <class T> struct X : Concrete, Holder<T>` passes. The upgrade is to visit instantiations.
  return llvm::all_of(Record->bases(), [](const CXXBaseSpecifier &Base) {
    const CXXRecordDecl *Parent = Base.getType()->getAsCXXRecordDecl();
    return !Parent || isPureInterface(Parent);
  });
}

// cplusp-multiple-inheritance: more than one direct base that is not a pure interface.
class MultipleInheritanceCheck : public SpelledCheck {
public:
  using SpelledCheck::SpelledCheck;
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(cxxRecordDecl(isDefinition(), unless(isImplicit())).bind("class"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    const auto *Class = Result.Nodes.getNodeAs<CXXRecordDecl>("class");
    if (Class->getNumBases() < 2)
      return;
    auto Heavy = llvm::count_if(Class->bases(), [](const CXXBaseSpecifier &Base) {
      const CXXRecordDecl *Parent = Base.getType()->getAsCXXRecordDecl();
      return Parent && !isPureInterface(Parent);
    });
    if (Heavy > 1)
      diag(Class->getLocation(), "more than one base is not a pure interface");
  }
};

AST_MATCHER(FunctionDecl, isOperatorFunction) { return Node.isOverloadedOperator(); }

// A parameter the function can write through: a non-const lvalue reference, a pointer to non-const, or a std::span of
// non-const elements, which writes through like a pointer.
const ClassTemplateSpecializationDecl *asSpan(QualType Type) {
  const auto *Span = dyn_cast_or_null<ClassTemplateSpecializationDecl>(Type.getNonReferenceType()->getAsCXXRecordDecl());
  return Span && Span->getName() == "span" && inStdNamespace(Span) ? Span : nullptr;
}

bool isMutableType(QualType Type) {
  Type = Type.getCanonicalType();
  if (const auto *Span = asSpan(Type))
    return !Span->getTemplateArgs()[0].getAsType().isConstQualified();
  return (Type->isLValueReferenceType() || Type->isPointerType()) && !Type->getPointeeType().isConstQualified();
}

bool isMutableParameter(const ParmVarDecl *Parameter) { return isMutableType(Parameter->getType()); }

bool hasMutableParameter(const FunctionDecl *Function) { return llvm::any_of(Function->parameters(), isMutableParameter); }

// A function that may change state: a non-static non-const member, or any function with a parameter it can write through.
// A static member has no object, so only its parameters count.
bool mayChangeState(const FunctionDecl *Function) {
  const auto *Method = dyn_cast<CXXMethodDecl>(Function);
  return (Method && !Method->isStatic() && !Method->isConst()) || hasMutableParameter(Function);
}

bool isAssignmentOrIncrement(OverloadedOperatorKind Operator) {
  switch (Operator) {
  case OO_Equal: case OO_PlusEqual: case OO_MinusEqual: case OO_StarEqual: case OO_SlashEqual: case OO_PercentEqual:
  case OO_AmpEqual: case OO_PipeEqual: case OO_CaretEqual: case OO_LessLessEqual: case OO_GreaterGreaterEqual:
  case OO_PlusPlus: case OO_MinusMinus:
    return true;
  default:
    return false;
  }
}

bool isImpureOperator(const FunctionDecl *Function) {
  return isAssignmentOrIncrement(Function->getOverloadedOperator()) || mayChangeState(Function);
}

// cplusp-impure-operator. An operator that the author defaulted or deleted is exempt, and so is every implicit one.
class ImpureOperatorCheck : public SpelledCheck {
public:
  using SpelledCheck::SpelledCheck;
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(functionDecl(isOperatorFunction(), unless(isImplicit()), unless(isDefaulted()), unless(isDeleted())).bind("operator"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    const auto *Function = Result.Nodes.getNodeAs<FunctionDecl>("operator");
    if (isImpureOperator(Function))
      diag(Function->getLocation(), "operator is not pure");
  }
};

// ponytail: a name test. The `__wrap_iter` of libc++ passes, and so does a pointer iterator, as in std::array,
// unless a begin call stores it. Code that depends on a template parameter passes too: `auto it = c.begin()` in a
// template body has no type yet, and instantiations are not visited. The upgrade is a list of the library's
// iterator types, or a test of iterator_category, and a visit of the instantiations.
AST_MATCHER(ValueDecl, hasIteratorType) {
  const CXXRecordDecl *Record = Node.getType().getNonReferenceType()->getAsCXXRecordDecl();
  return Record && Record->getName().contains("iterator");
}

// cplusp-iterator-arithmetic: (a) begin or end that is not a direct argument of a std call,
// (b) std::next, prev, advance and distance, (c) a variable, parameter or field of an iterator type.
class IteratorArithmeticCheck : public SpelledCheck {
public:
  using SpelledCheck::SpelledCheck;
  void registerMatchers(MatchFinder *Finder) override {
    const auto Bounds = anyOf(callee(cxxMethodDecl(hasAnyName("begin", "end", "cbegin", "cend", "rbegin", "rend", "crbegin", "crend"))),
                              callee(functionDecl(hasAnyName("::std::begin", "::std::end", "::std::cbegin", "::std::cend", "::std::rbegin",
                                                             "::std::rend", "::std::crbegin", "::std::crend"))));
    Finder->addMatcher(callExpr(Bounds, unless(hasParent(stdCall()))).bind("call"), this);
    Finder->addMatcher(callExpr(callee(functionDecl(hasAnyName("::std::next", "::std::prev", "::std::advance", "::std::distance")))).bind("call"), this);
    Finder->addMatcher(valueDecl(anyOf(varDecl(), fieldDecl()), hasIteratorType()).bind("decl"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    if (const auto *Call = Result.Nodes.getNodeAs<CallExpr>("call"))
      diag(Call->getBeginLoc(), "iterator function outside a std call");
    else
      diag(Result.Nodes.getNodeAs<ValueDecl>("decl")->getLocation(), "stored iterator");
  }
};

// A capture by reference, or of `this` by pointer. `[*this]` copies the object and passes.
AST_MATCHER(LambdaExpr, capturesByReferenceOrThis) {
  return llvm::any_of(Node.captures(), [](const LambdaCapture &Capture) {
    return Capture.getCaptureKind() == LCK_ByRef || Capture.getCaptureKind() == LCK_This;
  });
}

// A lambda marked `mutable`. Its call changes its own captures, so it carries state between calls.
AST_MATCHER(LambdaExpr, isMutableLambda) { return Node.isMutable(); }

// cplusp-lambda-limits: a lambda that is no direct argument of a std call, that captures by reference or `this`,
// or that is `mutable`.
class LambdaLimitsCheck : public SpelledCheck {
public:
  using SpelledCheck::SpelledCheck;
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(lambdaExpr(anyOf(unless(hasParent(stdCall())), capturesByReferenceOrThis(), isMutableLambda())).bind("lambda"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    diag(Result.Nodes.getNodeAs<LambdaExpr>("lambda")->getBeginLoc(), "lambda is outside its limits");
  }
};

// ------------------------------------------------------------ roots, decision 0033

// A name for an object: a variable, `this` or the State, then the members under it. The State stands for all that a call
// may reach. `Global` is set when the first step is a global or a static data member that is not const.
const char StateKey = 0, ThisKey = 0;

struct RootPath {
  std::vector<const void *> Steps;
  bool Global = false;
};
using Roots = llvm::SmallVector<RootPath, 2>;

RootPath stateRoot() { return {{&StateKey}, false}; }

// Equal, or one a prefix of the other: the two reach the same storage.
bool related(const RootPath &A, const RootPath &B) {
  const auto Shared = std::min(A.Steps.size(), B.Steps.size());
  return std::equal(A.Steps.begin(), A.Steps.begin() + Shared, B.Steps.begin());
}

bool conflict(const Roots &A, const Roots &B) {
  return llvm::any_of(A, [&](const RootPath &P) { return llvm::any_of(B, [&](const RootPath &Q) { return related(P, Q); }); });
}

// What the walk of an expression found. `ConstHandle` is set when the path passes through the `operator*`, `operator->`
// or `get` of a const unique_ptr or shared_ptr.
struct Walk {
  Roots Paths;
  bool ConstHandle = false;
  void add(const Walk &Other) {
    Paths.append(Other.Paths.begin(), Other.Paths.end());
    ConstHandle |= Other.ConstHandle;
  }
};

bool isStdClass(QualType Type, std::initializer_list<StringRef> Names) {
  const CXXRecordDecl *Record = Type.getNonReferenceType()->getAsCXXRecordDecl();
  return Record && Record->getDeclName().isIdentifier() && inStdNamespace(Record) && llvm::is_contained(Names, Record->getName());
}

bool isOwner(QualType Type) { return isStdClass(Type, {"unique_ptr", "shared_ptr"}); }
bool isHandle(QualType Type) { return isStdClass(Type, {"unique_ptr", "shared_ptr", "optional"}); }

// A std function whose result is the object, or part of it. The root of the result is the root of the object, or of the first
// argument of a free function. `move`, `forward` and `as_const` are casts.
bool keepsRoot(const FunctionDecl *Function) {
  return inStdNamespace(Function) && Function->getDeclName().isIdentifier() &&
         llvm::is_contained({"front", "back", "at", "data", "begin", "end", "cbegin", "cend", "rbegin", "rend", "crbegin", "crend", "get",
                             "subspan", "first", "last", "move", "forward", "as_const"},
                            Function->getName());
}

// The object of a member call, or of an operator that is a member. Null for a free function and a static member.
const Expr *objectOf(const CallExpr *Call) {
  const auto *Method = dyn_cast_or_null<CXXMethodDecl>(Call->getDirectCallee());
  if (!Method || Method->isStatic())
    return nullptr;
  if (const auto *Member = dyn_cast<CXXMemberCallExpr>(Call))
    return Member->getImplicitObjectArgument();
  return isa<CXXOperatorCallExpr>(Call) ? Call->getArg(0) : nullptr;
}

// What a parameter writes through, for the rule of one writer. A parameter of rvalue reference type writes too: `f(std::move(a),
// std::move(a))` moves one object twice. A forwarding reference has its instantiated type here, so it counts when it is non-const.
bool writesThrough(QualType Type) {
  return isMutableType(Type) || (Type->isRValueReferenceType() && !Type->getPointeeType().isConstQualified());
}

bool bindsToName(QualType Type) { return Type->isReferenceType() || Type->isPointerType() || asSpan(Type); }

// A global or a static data member is State. A constant is not: nothing writes it, so it is no second name for anything,
// and a read of it beside a change reads nothing the change can reach.
bool isMutableGlobal(const VarDecl *Var) { return Var->hasGlobalStorage() && !Var->getType().isConstQualified(); }

// An argument that names an object: it binds to a reference, a pointer or a span, or it is the object of a member call.
struct Arg {
  Walk Where;
  bool Writes;
  bool Object;
  bool ConstRefIntoStd;  // a const reference to a function or class of std, which has no way to reach the State
};

Walk rootsOf(const Expr *E);
void collectArgs(const Expr *Node, llvm::SmallVectorImpl<Arg> &Out);

// The hidden variables of a range-for, and a loop variable that is a reference, are names for the range. The loop variable is
// `*__begin`, and `__begin` is `__range.begin()`, and `__range` is the range expression.
Walk rangeRoots(const VarDecl *Var) {
  const Expr *Init = Var->getInit()->IgnoreParenImpCasts();
  if (Var->isCXXForRangeDecl()) {
    if (const auto *Star = dyn_cast<CXXOperatorCallExpr>(Init); Star && Star->getOperator() == OO_Star)
      return rootsOf(Star->getArg(0));
    if (const auto *Deref = dyn_cast<UnaryOperator>(Init))
      return rootsOf(Deref->getSubExpr());
  } else if (const auto *Call = dyn_cast<CallExpr>(Init)) {
    if (const Expr *Object = objectOf(Call))
      return rootsOf(Object);
    return Call->getNumArgs() ? rootsOf(Call->getArg(0)) : Walk();
  }
  return rootsOf(Init);
}

// ponytail: three ceilings. A reference local is a name of its own, and the row lvalue_references bans it, so the walk does not
// follow it to its initializer. A structured binding is its own root. A call that returns a pointer or a span by value, and a call
// through a function pointer, have a fresh root, so two spans cut by one user function from one buffer are missed.
// Upgrade: follow the initializer of a reference local, and treat a returned pointer or span like a returned reference.
Walk rootsOf(const Expr *E) {
  Walk W;
  if (!E)
    return W;
  E = E->IgnoreParens();
  if (const auto *Cast = dyn_cast<CastExpr>(E)) {
    switch (Cast->getCastKind()) {
    case CK_NoOp: case CK_LValueToRValue: case CK_ArrayToPointerDecay: case CK_DerivedToBase: case CK_UncheckedDerivedToBase:
    case CK_BaseToDerived: case CK_Dynamic: case CK_BitCast: case CK_LValueBitCast: case CK_ConstructorConversion:
    case CK_UserDefinedConversion:
      return rootsOf(Cast->getSubExpr());
    default:
      return W;
    }
  }
  if (const auto *Full = dyn_cast<FullExpr>(E))
    return rootsOf(Full->getSubExpr());
  if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(E))
    return rootsOf(Temporary->getSubExpr());
  if (const auto *Bind = dyn_cast<CXXBindTemporaryExpr>(E))
    return rootsOf(Bind->getSubExpr());
  if (const auto *Ref = dyn_cast<DeclRefExpr>(E)) {
    if (const auto *Var = dyn_cast<VarDecl>(Ref->getDecl())) {
      if (Var->hasInit() && (Var->isImplicit() || (Var->isCXXForRangeDecl() && Var->getType()->isReferenceType())))
        return rangeRoots(Var);
      W.Paths.push_back({{Var}, isMutableGlobal(Var)});
    } else if (isa<BindingDecl>(Ref->getDecl())) {
      W.Paths.push_back({{Ref->getDecl()}, false});
    }
    return W;
  }
  if (isa<CXXThisExpr>(E)) {
    W.Paths.push_back({{&ThisKey}, false});
    return W;
  }
  if (const auto *Member = dyn_cast<MemberExpr>(E)) {
    if (const auto *Var = dyn_cast<VarDecl>(Member->getMemberDecl())) {
      W.Paths.push_back({{Var}, isMutableGlobal(Var)});
    } else if (isa<FieldDecl>(Member->getMemberDecl())) {
      W = rootsOf(Member->getBase());
      for (RootPath &Path : W.Paths)
        Path.Steps.push_back(Member->getMemberDecl());
    }
    return W;
  }
  if (const auto *Subscript = dyn_cast<ArraySubscriptExpr>(E))
    return rootsOf(Subscript->getBase());
  if (const auto *Unary = dyn_cast<UnaryOperator>(E)) {
    switch (Unary->getOpcode()) {
    case UO_Deref: case UO_AddrOf: case UO_PreInc: case UO_PreDec: case UO_Extension:
      return rootsOf(Unary->getSubExpr());
    default:
      return W;
    }
  }
  if (const auto *Binary = dyn_cast<BinaryOperator>(E)) {
    if (Binary->isAssignmentOp())
      return rootsOf(Binary->getLHS());
    if (Binary->isCommaOp())
      return rootsOf(Binary->getRHS());
    if (Binary->getType()->isPointerType())
      return rootsOf(Binary->getLHS()->getType()->isPointerType() ? Binary->getLHS() : Binary->getRHS());
    return W;
  }
  if (const auto *Conditional = dyn_cast<AbstractConditionalOperator>(E)) {
    W = rootsOf(Conditional->getTrueExpr());
    W.add(rootsOf(Conditional->getFalseExpr()));
    return W;
  }
  if (const auto *Construct = dyn_cast<CXXConstructExpr>(E))
    return asSpan(Construct->getType()) && Construct->getNumArgs() ? rootsOf(Construct->getArg(0)) : W;
  const auto *Call = dyn_cast<CallExpr>(E);
  const FunctionDecl *Function = Call ? Call->getDirectCallee() : nullptr;
  if (!Function)
    return W;
  const Expr *Object = objectOf(Call);
  const OverloadedOperatorKind Operator = Function->getOverloadedOperator();
  const bool Deref = Object && isHandle(Object->getType()) && (Operator == OO_Star || Operator == OO_Arrow);
  if (Object && (Deref || Operator == OO_Subscript || keepsRoot(Function))) {
    W = rootsOf(Object);
    // The owner is const as declared, not as the implicit cast to the const operator makes it. A write through `get()` is as
    // much a write through the handle as one through `*`.
    const QualType Owner = Object->IgnoreParenImpCasts()->getType();
    if (Owner.isConstQualified() && isOwner(Owner) && (Deref || Function->getName() == "get"))
      W.ConstHandle = true;
    return W;
  }
  if (!Object && keepsRoot(Function))
    return Call->getNumArgs() ? rootsOf(Call->getArg(0)) : W;
  if (Function->getReturnType()->isReferenceType()) {
    // Any reference may be one of the arguments, or something the State holds.
    llvm::SmallVector<Arg, 4> Args;
    collectArgs(Call, Args);
    for (const Arg &A : Args)
      W.add(A.Where);
    W.Paths.push_back(stateRoot());
  }
  return W;
}

// The arguments of a call that name an object: each one that binds to a reference, a pointer or a span, and the object of a
// member call. An argument by value is a copy, so it is no name. A constructor has no object.
void collectArgs(const Expr *Node, llvm::SmallVectorImpl<Arg> &Out) {
  const FunctionDecl *Function = nullptr;
  llvm::SmallVector<const Expr *, 4> Args;
  if (const auto *Call = dyn_cast<CallExpr>(Node)) {
    Function = Call->getDirectCallee();
    Args.assign(Call->arg_begin(), Call->arg_end());
    if (const Expr *Object = objectOf(Call)) {
      Out.push_back({rootsOf(Object), !cast<CXXMethodDecl>(Function)->isConst(), true, false});
      if (isa<CXXOperatorCallExpr>(Call))
        Args.erase(Args.begin());
    }
  } else if (const auto *Construct = dyn_cast<CXXConstructExpr>(Node)) {
    Function = Construct->getConstructor();
    Args.assign(Construct->arg_begin(), Construct->arg_end());
  }
  if (!Function)
    return;
  for (unsigned I = 0; I < Args.size() && I < Function->getNumParams(); ++I) {
    const QualType Type = Function->getParamDecl(I)->getType();
    if (bindsToName(Type))
      Out.push_back({rootsOf(Args[I]), writesThrough(Type), false,
                     Type->isReferenceType() && Type->getPointeeType().isConstQualified() && inStdNamespace(Function)});
  }
}

// cplusp-aliasing: decision 0033. When one argument of a call can write, no two arguments reach one object.
// A global bound to a reference, a pointer or a span is refused on its own, because it is the State as well. A const reference
// to a global in a call into std is the one exception: nothing in std can reach the State.
class AliasingCheck : public SpelledCheck {
public:
  using SpelledCheck::SpelledCheck;
  void registerMatchers(MatchFinder *Finder) override { Finder->addMatcher(expr(anyOf(callExpr(), cxxConstructExpr())).bind("call"), this); }
  void check(const MatchFinder::MatchResult &Result) override {
    const auto *Node = Result.Nodes.getNodeAs<Expr>("call");
    llvm::SmallVector<Arg, 4> Args;
    collectArgs(Node, Args);
    if (llvm::any_of(Args, [](const Arg &A) {
          return !A.Object && !A.ConstRefIntoStd && llvm::any_of(A.Where.Paths, [](const RootPath &P) { return P.Global; });
        }))
      diag(Node->getBeginLoc(), "a global passed by reference");
    if (!llvm::any_of(Args, [](const Arg &A) { return A.Writes; }))
      return;
    for (size_t I = 0; I < Args.size(); ++I)
      for (size_t J = I + 1; J < Args.size(); ++J)
        if (conflict(Args[I].Where.Paths, Args[J].Where.Paths)) {
          diag(Node->getBeginLoc(), "two names for one object in one call");
          return;
        }
  }
};

// cplusp-const-handle: decision 0033. A write whose path passes through a const unique_ptr or shared_ptr. A write is an
// assignment, an increment, a non-const member call, or a binding to a non-const reference, pointer or span.
class ConstHandleCheck : public SpelledCheck {
public:
  using SpelledCheck::SpelledCheck;
  void registerMatchers(MatchFinder *Finder) override { Finder->addMatcher(expr().bind("expr"), this); }
  void check(const MatchFinder::MatchResult &Result) override {
    const auto *Node = Result.Nodes.getNodeAs<Expr>("expr");
    bool Writes = false;
    if (const auto *Binary = dyn_cast<BinaryOperator>(Node)) {
      Writes = Binary->isAssignmentOp() && rootsOf(Binary->getLHS()).ConstHandle;
    } else if (const auto *Unary = dyn_cast<UnaryOperator>(Node)) {
      Writes = Unary->isIncrementDecrementOp() && rootsOf(Unary->getSubExpr()).ConstHandle;
    } else if (isa<CallExpr, CXXConstructExpr>(Node)) {
      llvm::SmallVector<Arg, 4> Args;
      collectArgs(Node, Args);
      Writes = llvm::any_of(Args, [](const Arg &A) { return A.Writes && A.Where.ConstHandle; });
    }
    if (Writes)
      diag(Node->getBeginLoc(), "a write through a const handle");
  }
};

// Names in std that return an iterator, a reference, a cast or a new value and change nothing, though the object or the argument
// is non-const. A forwarding reference instantiates as a non-const reference, which is why `make_pair` and `get` are here.
// So `std::sort(v.begin(), v.end())`, `v.front() + v.back()` and `f(std::move(a), std::move(b))` are no pair of changes.
// A function of the same name outside std is a change.
bool changesNothing(const FunctionDecl *Function) {
  return inStdNamespace(Function) && Function->getDeclName().isIdentifier() &&
         llvm::is_contained({"begin", "end", "cbegin", "cend", "rbegin", "rend", "crbegin", "crend", "at", "front", "back", "move", "forward",
                             "as_const", "make_pair", "make_tuple", "get", "tie"},
                            Function->getName());
}

// A node that changes state: an assignment, an increment, a call of a function that may change state, or a construction
// with a parameter the constructor can write through. A std::span is a view, and cutting one changes nothing, so
// `fill(v, v)` is a matter for the row aliasing. An operator call is judged by its callee only for `()`. Any other
// operator counts as an assignment or an increment, so `v[i]` on a non-const vector is no change.
bool isChange(const Stmt *S) {
  if (const auto *Unary = dyn_cast<UnaryOperator>(S))
    return Unary->isIncrementDecrementOp();
  if (const auto *Binary = dyn_cast<BinaryOperator>(S))
    return Binary->isAssignmentOp();
  if (const auto *Construct = dyn_cast<CXXConstructExpr>(S))
    return !asSpan(Construct->getType()) && hasMutableParameter(Construct->getConstructor());
  if (const auto *Operator = dyn_cast<CXXOperatorCallExpr>(S))
    if (Operator->getOperator() != OO_Call)
      return isAssignmentOrIncrement(Operator->getOperator());
  if (const auto *Call = dyn_cast<CallExpr>(S))
    return Call->getDirectCallee() && !changesNothing(Call->getDirectCallee()) && mayChangeState(Call->getDirectCallee());
  return false;
}

// ponytail: three ceilings. A lambda changes nothing where it is written, so a capture initializer that does is missed.
// A reference member lets a const method change state, and the check calls that method pure. A call through a template
// parameter has no callee the check can read, and so has a call through a function pointer or a member pointer.
// Upgrade: count the capture initializers, and visit instantiations.
// An unevaluated operand changes nothing: `sizeof`, `alignof`, `noexcept` and `typeid` do not run it.
bool changes(const Stmt *S) {
  if (isa<LambdaExpr, UnaryExprOrTypeTraitExpr, CXXNoexceptExpr, CXXTypeidExpr>(S))
    return false;
  return isChange(S) || llvm::any_of(S->children(), [](const Stmt *Child) { return Child && changes(Child); });
}

// The children of a node that the standard leaves unordered among themselves. Everything else is ordered,
// so two changes in it are not a finding. A coroutine suspend orders its parts. A node kind that is not named here has unordered children.
llvm::SmallVector<const Stmt *, 4> unorderedChildren(const Stmt *S) {
  llvm::SmallVector<const Stmt *, 4> Children;
  if (const auto *Operator = dyn_cast<CXXOperatorCallExpr>(S)) {
    // The built-in order of an operator holds when it is overloaded, and for a call, the callee comes first.
    switch (Operator->getOperator()) {
    case OO_Equal: case OO_PlusEqual: case OO_MinusEqual: case OO_StarEqual: case OO_SlashEqual: case OO_PercentEqual:
    case OO_AmpEqual: case OO_PipeEqual: case OO_CaretEqual: case OO_LessLessEqual: case OO_GreaterGreaterEqual:
    case OO_LessLess: case OO_GreaterGreater: case OO_Subscript: case OO_ArrowStar:
    case OO_AmpAmp: case OO_PipePipe: case OO_Comma:
      return Children;
    case OO_Call:
      Children.assign(Operator->arg_begin() + 1, Operator->arg_end());
      return Children;
    default:
      break;
    }
    Children.assign(Operator->arg_begin(), Operator->arg_end());
  } else if (const auto *Call = dyn_cast<CallExpr>(S)) {
    Children.assign(Call->arg_begin(), Call->arg_end());
  } else if (const auto *Construct = dyn_cast<CXXConstructExpr>(S)) {
    if (!Construct->isListInitialization())
      Children.assign(Construct->arg_begin(), Construct->arg_end());
  } else if (const auto *Lambda = dyn_cast<LambdaExpr>(S)) {
    // Only the capture initializers run where the lambda is written. The body runs when it is called.
    Children.assign(Lambda->capture_init_begin(), Lambda->capture_init_end());
  } else if (const auto *Binary = dyn_cast<BinaryOperator>(S)) {
    if (!Binary->isAssignmentOp() && !Binary->isCommaOp() && !Binary->isLogicalOp() && !Binary->isShiftOp() && !Binary->isPtrMemOp())
      Children = {Binary->getLHS(), Binary->getRHS()};
  } else if (!isa<AbstractConditionalOperator>(S) && !isa<ArraySubscriptExpr>(S) && !isa<InitListExpr>(S) && !isa<MemberExpr>(S) &&
             !isa<CoroutineSuspendExpr>(S)) {
    Children.assign(S->child_begin(), S->child_end());
  }
  return Children;
}

// What a subtree writes and what it reads, as root paths, for the read rule of decision 0033. A call may touch the State, so
// any call puts the State in both sets. A global does too. An unevaluated operand and a lambda body do nothing here.
struct Effects {
  Roots Writes, Reads;
};

void addPaths(Roots &Into, const Roots &Paths) {
  for (const RootPath &Path : Paths) {
    Into.push_back(Path);
    if (Path.Global)
      Into.push_back(stateRoot());
  }
}

// A trivial special member, such as the implicit copy of a struct, runs no code.
bool isRealCall(const Stmt *S) {
  const FunctionDecl *Function = nullptr;
  if (const auto *Call = dyn_cast<CallExpr>(S))
    Function = Call->getDirectCallee();
  else if (const auto *Construct = dyn_cast<CXXConstructExpr>(S))
    Function = Construct->getConstructor();
  return !Function || !Function->isTrivial();
}

void effects(const Stmt *S, Effects &E) {
  if (!S || isa<LambdaExpr, UnaryExprOrTypeTraitExpr, CXXNoexceptExpr, CXXTypeidExpr>(S))
    return;
  if (isa<DeclRefExpr, MemberExpr, CXXThisExpr>(S))
    addPaths(E.Reads, rootsOf(cast<Expr>(S)).Paths);
  if (isa<CallExpr, CXXConstructExpr>(S)) {
    if (isRealCall(S)) {
      E.Reads.push_back(stateRoot());
      E.Writes.push_back(stateRoot());
    }
    llvm::SmallVector<Arg, 4> Args;
    collectArgs(cast<Expr>(S), Args);
    for (const Arg &A : Args)
      if (A.Writes)
        addPaths(E.Writes, A.Where.Paths);
  }
  if (const auto *Binary = dyn_cast<BinaryOperator>(S); Binary && Binary->isAssignmentOp())
    addPaths(E.Writes, rootsOf(Binary->getLHS()).Paths);
  if (const auto *Unary = dyn_cast<UnaryOperator>(S); Unary && Unary->isIncrementDecrementOp())
    addPaths(E.Writes, rootsOf(Unary->getSubExpr()).Paths);
  for (const Stmt *Child : S->children())
    effects(Child, E);
}

// cplusp-evaluation-order: a node with two unordered children that each change state, decision 0026. When exactly one changes
// state, no other unordered child reads what the change can reach, decision 0033.
class EvaluationOrderCheck : public SpelledCheck {
public:
  using SpelledCheck::SpelledCheck;
  void registerMatchers(MatchFinder *Finder) override { Finder->addMatcher(expr().bind("expr"), this); }
  void check(const MatchFinder::MatchResult &Result) override {
    const auto *Node = Result.Nodes.getNodeAs<Expr>("expr");
    auto Children = unorderedChildren(Node);
    auto Changing = llvm::make_filter_range(Children, [](const Stmt *Child) { return Child && changes(Child); });
    const auto Count = std::distance(Changing.begin(), Changing.end());
    if (Count > 1) {
      diag(Node->getBeginLoc(), "two changes of state without an order");
    } else if (Count == 1) {
      const Stmt *Changer = *Changing.begin();
      Effects Change;
      effects(Changer, Change);
      for (const Stmt *Child : Children) {
        Effects Other;
        if (Child != Changer)
          effects(Child, Other);
        if (conflict(Change.Writes, Other.Reads)) {
          diag(Node->getBeginLoc(), "a read beside an unordered change of state");
          return;
        }
      }
    }
  }
};

// cplusp-inexact-literal: a floating-point literal whose spelling does not convert to its own type without loss.
// The compiler's float library decides. A hex float, 0.5 and 1e3 are exact. 0.1 is not.
class InexactLiteralCheck : public SpelledCheck {
public:
  using SpelledCheck::SpelledCheck;
  void registerMatchers(MatchFinder *Finder) override { Finder->addMatcher(floatLiteral().bind("literal"), this); }
  void check(const MatchFinder::MatchResult &Result) override {
    const auto *Literal = Result.Nodes.getNodeAs<FloatingLiteral>("literal");
    SourceLocation Loc = Literal->getBeginLoc();
    // The token as written, also when a macro such as DBL_EPSILON holds it.
    llvm::SmallString<32> Buffer;
    std::string Spelling =
        Lexer::getSpelling(Result.SourceManager->getSpellingLoc(Loc), Buffer, *Result.SourceManager, Result.Context->getLangOpts()).str();
    // A digit separator and a user suffix are no part of the number. Then the suffix f, F, l or L.
    llvm::erase(Spelling, '\'');
    Spelling = Spelling.substr(0, Spelling.find('_'));
    StringRef Text = StringRef(Spelling).rtrim("fFlL");
    llvm::APFloat Value(Result.Context->getFloatTypeSemantics(Literal->getType()));
    auto Status = Value.convertFromString(Text, llvm::APFloat::rmNearestTiesToEven);
    if (!Status) {
      llvm::consumeError(Status.takeError());
      return;
    }
    if (*Status & llvm::APFloat::opInexact)
      diag(Result.SourceManager->getFileLoc(Loc), "floating-point literal is not exactly a double");
  }
};

class CplusPModule : public ClangTidyModule {
public:
  void addCheckFactories(ClangTidyCheckFactories &Factories) override {
    Factories.registerCheck<MatcherCheck>("cplusp-matcher");
    Factories.registerCheck<MutableCheck>("cplusp-mutable");
    Factories.registerCheck<MultipleInheritanceCheck>("cplusp-multiple-inheritance");
    Factories.registerCheck<ImpureOperatorCheck>("cplusp-impure-operator");
    Factories.registerCheck<IteratorArithmeticCheck>("cplusp-iterator-arithmetic");
    Factories.registerCheck<LambdaLimitsCheck>("cplusp-lambda-limits");
    Factories.registerCheck<EvaluationOrderCheck>("cplusp-evaluation-order");
    Factories.registerCheck<AliasingCheck>("cplusp-aliasing");
    Factories.registerCheck<ConstHandleCheck>("cplusp-const-handle");
    Factories.registerCheck<InexactLiteralCheck>("cplusp-inexact-literal");
  }
};

} // namespace

static clang::tidy::ClangTidyModuleRegistry::Add<CplusPModule> X("cplusp-module", "Adds the checks of cplusp.");

// Forces a linker to keep this module when it is linked in. A loaded plugin does not need it.
volatile int CplusPModuleAnchorSource = 0;
