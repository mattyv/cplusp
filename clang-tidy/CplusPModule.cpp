// The clang-tidy plugin of cplusp. See docs/policy.md.
//
// One generic check, driven by the policy file.
// The gate writes each `matcher` entry of a rule as an option of the check, named `{rule_id}/{n}`.
// The check compiles the pattern and reports every match with the rule id as its message.
// The Rust side turns the rule id into the message for the bot.
//
// Eleven hand-written checks, for the rules that a pattern cannot say. The gate maps a finding to its rule by
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
#include <set>
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

const ClassTemplateSpecializationDecl *asSpan(QualType Type) {
  const auto *Span = dyn_cast_or_null<ClassTemplateSpecializationDecl>(Type.getNonReferenceType()->getAsCXXRecordDecl());
  return Span && Span->getName() == "span" && inStdNamespace(Span) ? Span : nullptr;
}

// A parameter type the function can write through: a non-const lvalue reference, a pointer to non-const, or a std::span of
// non-const elements, which writes through like a pointer.
bool isMutableType(QualType Type) {
  Type = Type.getCanonicalType();
  if (const auto *Span = asSpan(Type))
    return !Span->getTemplateArgs()[0].getAsType().isConstQualified();
  return (Type->isLValueReferenceType() || Type->isPointerType()) && !Type->getPointeeType().isConstQualified();
}

bool hasMutableParameter(const FunctionDecl *Function) {
  return llvm::any_of(Function->parameters(), [](const ParmVarDecl *Parameter) { return isMutableType(Parameter->getType()); });
}

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
  const Expr *At = nullptr;  // the expression that names the variable, for a path that starts at one
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

// What the walk of an expression found. `ConstHandle` is set when the path passes through the `operator*`, `operator->`, `get`
// or the subscript of an array owner, of a const unique_ptr or shared_ptr.
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
// and a read of it beside a change reads nothing the change can reach. A global that a system header declares, such as `std::cout`, is
// the business of the row iostreams and not of the rules about State. The location decides, not the namespace: a `namespace std`
// that the file opens itself holds state.
bool isMutableGlobal(const VarDecl *Var) {
  return Var->hasGlobalStorage() && !Var->getType().isConstQualified() &&
         !Var->getASTContext().getSourceManager().isInSystemHeader(Var->getLocation());
}

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

// A function is in std when it is declared there, or when the call names it there: `std::memcpy` is `::memcpy` that a using
// declaration brings into std, and the call is a call into std.
bool namedInStd(const CallExpr *Call, const FunctionDecl *Function) {
  if (inStdNamespace(Function))
    return true;
  const auto *Ref = dyn_cast<DeclRefExpr>(Call->getCallee()->IgnoreParenImpCasts());
  return Ref && inStdNamespace(Ref->getFoundDecl());
}

// A function that this file does not define, and std does not own, may return a reference, a pointer or a span to any global: it
// reaches the State again. A function that this file defines has had its returns checked, so it returns only what its arguments reach.
bool hiddenReference(const CallExpr *Call, const FunctionDecl *Function) {
  return bindsToName(Function->getReturnType()) && !namedInStd(Call, Function) && !Function->isImplicit() && !Function->isDefaulted() &&
         !Function->isDefined();
}

// ponytail: three ceilings. A reference local is a name of its own, and the row lvalue_references bans it, so the walk does not
// follow it to its initializer. A structured binding is its own root. A call through a function pointer has a fresh root.
// Upgrade: follow the initializer of a reference local and of a binding, and read the type of a function pointer.
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
  if (const auto *Default = dyn_cast<CXXDefaultArgExpr>(E))
    return rootsOf(Default->getExpr());
  if (const auto *Bind = dyn_cast<CXXBindTemporaryExpr>(E))
    return rootsOf(Bind->getSubExpr());
  if (const auto *Ref = dyn_cast<DeclRefExpr>(E)) {
    if (const auto *Var = dyn_cast<VarDecl>(Ref->getDecl())) {
      if (Var->hasInit() && (Var->isImplicit() || (Var->isCXXForRangeDecl() && Var->getType()->isReferenceType())))
        return rangeRoots(Var);
      W.Paths.push_back({{Var}, isMutableGlobal(Var), Ref});
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
      W.Paths.push_back({{Var}, isMutableGlobal(Var), Member});
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
  // An allocation function returns new memory, which no other name reaches.
  if (!Function || Function->isReplaceableGlobalAllocationFunction())
    return W;
  const Expr *Object = objectOf(Call);
  const OverloadedOperatorKind Operator = Function->getOverloadedOperator();
  const bool Deref = Object && isHandle(Object->getType()) && (Operator == OO_Star || Operator == OO_Arrow);
  if (Object && (Deref || Operator == OO_Subscript || keepsRoot(Function))) {
    W = rootsOf(Object);
    // The owner is const as declared, not as the implicit cast to the const operator makes it. A write through `get()` or
    // through the subscript of an array owner is as much a write through the handle as one through `*`. An operator has no name.
    const QualType Owner = Object->IgnoreParenImpCasts()->getType();
    const bool Get = Function->getDeclName().isIdentifier() && Function->getName() == "get";
    if (Owner.isConstQualified() && isOwner(Owner) && (Deref || Get || Operator == OO_Subscript))
      W.ConstHandle = true;
    return W;
  }
  if (!Object && keepsRoot(Function))
    return Call->getNumArgs() ? rootsOf(Call->getArg(0)) : W;
  if (bindsToName(Function->getReturnType())) {
    // A reference, pointer or span that a function returns reaches only what its arguments and its object reach. The return check
    // refuses a function that returns a global, so no caller receives one. A function from outside this file is the exception.
    llvm::SmallVector<Arg, 4> Args;
    collectArgs(Call, Args);
    for (const Arg &A : Args)
      W.add(A.Where);
    if (hiddenReference(Call, Function)) {
      RootPath Hidden = stateRoot();
      Hidden.At = Call;
      W.Paths.push_back(Hidden);
    }
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

// A function that the semantic checks do not judge: the dependent pattern of a template, which is judged at each instantiation where
// every type and every callee is known, and the body of an implicit function, which the compiler wrote. A lambda's call operator is
// implicit and is judged, because the lambda runs where it is written. Decision 0036.
AST_MATCHER(FunctionDecl, notJudged) {
  const auto *Method = dyn_cast<CXXMethodDecl>(&Node);
  return Node.isDependentContext() || (Node.isImplicit() && !(Method && Method->getParent()->isLambda()));
}

// The matchers of the semantic checks: a node in a user file, and not in a function that is not judged. The checks read the tree as the
// compiler has it, with the instantiations of a template.
auto judged() { return allOf(unless(isExpansionInSystemHeader()), unless(forFunction(notJudged()))); }

// cplusp-aliasing: decision 0033. When one argument of a call can write, no two arguments reach one object.
// A global bound to a reference, a pointer or a span is refused on its own, because it is the State as well. A const reference
// to a global in a call into std is the one exception: nothing in std can reach the State. A function that returns a reference,
// a pointer or a span may return only what its parameters or `this` reach, else every call of it passes a global.
class AliasingCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(expr(anyOf(callExpr(), cxxConstructExpr()), judged()).bind("call"), this);
    Finder->addMatcher(returnStmt(forFunction(functionDecl(unless(notJudged())).bind("function"))).bind("return"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    if (const auto *Return = Result.Nodes.getNodeAs<ReturnStmt>("return")) {
      // A function that returns a reference, a pointer or a span may return only what its parameters or `this` reach. A global,
      // or a reference from a function this file does not define, that escapes this way is a global passed by reference at every
      // call of the function.
      const auto *Function = Result.Nodes.getNodeAs<FunctionDecl>("function");
      if (Return->getRetValue() && bindsToName(Function->getReturnType()) &&
          llvm::any_of(rootsOf(Return->getRetValue()).Paths, [](const RootPath &P) { return P.Global || P.Steps[0] == &StateKey; }))
        diag(Return->getBeginLoc(), "a reference to a global escapes");
      return;
    }
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
class ConstHandleCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void registerMatchers(MatchFinder *Finder) override { Finder->addMatcher(expr(judged()).bind("expr"), this); }
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

// Whether a call of `Function` may change a global: it lists one on its `modifies` line, its body or the body of something it calls
// writes one, or it is outside std with no body here and no contract lines. Defined with the state check, which reads the same lines.
bool reachesState(const FunctionDecl *Function);
void resetReach();

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
    // A constructor of a system header builds a std object. The compiler builds some of them for a rewritten comparison, such as
    // the `__unspec` of `o < 5` on an optional, and no author wrote them.
    return !asSpan(Construct->getType()) && !Construct->getConstructor()->getASTContext().getSourceManager().isInSystemHeader(Construct->getConstructor()->getLocation()) &&
           (hasMutableParameter(Construct->getConstructor()) || reachesState(Construct->getConstructor()));
  if (const auto *Operator = dyn_cast<CXXOperatorCallExpr>(S))
    if (Operator->getOperator() != OO_Call)
      return isAssignmentOrIncrement(Operator->getOperator());
  if (const auto *Call = dyn_cast<CallExpr>(S)) {
    const FunctionDecl *Callee = Call->getDirectCallee();
    return Callee && !changesNothing(Callee) && (mayChangeState(Callee) || reachesState(Callee));
  }
  return false;
}

// ponytail: three ceilings. A lambda changes nothing where it is written, so a capture initializer that does is missed.
// A reference member lets a const method change state, and the check calls that method pure. A call through a function pointer
// or a member pointer has no callee the check can read.
// Upgrade: count the capture initializers, and read the type of a pointer.
// An unevaluated operand changes nothing: `sizeof`, `alignof`, `noexcept` and `typeid` do not run it.
// A default argument has no children of its own, and the call runs its expression.
bool changes(const Stmt *S) {
  if (isa<LambdaExpr, UnaryExprOrTypeTraitExpr, CXXNoexceptExpr, CXXTypeidExpr>(S))
    return false;
  if (const auto *Default = dyn_cast<CXXDefaultArgExpr>(S))
    return changes(Default->getExpr());
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
  if (!S || isa<UnaryExprOrTypeTraitExpr, CXXNoexceptExpr, CXXTypeidExpr>(S))
    return;
  // Where a lambda is written only its capture initializers run. A default argument has no children of its own.
  if (const auto *Lambda = dyn_cast<LambdaExpr>(S)) {
    for (const Expr *Init : Lambda->capture_inits())
      effects(Init, E);
    return;
  }
  if (const auto *Default = dyn_cast<CXXDefaultArgExpr>(S)) {
    effects(Default->getExpr(), E);
    return;
  }
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
class EvaluationOrderCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void onStartOfTranslationUnit() override { resetReach(); }
  void registerMatchers(MatchFinder *Finder) override { Finder->addMatcher(expr(judged()).bind("expr"), this); }
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

// cplusp-allowlist: decision 0032. The gate refuses every kind of node it does not know. The options are three lists of allowed kinds,
// `statements`, `declarations` and `types`, a list of allowed attributes, `attributes`, and one option per row of the policy,
// `{row}: kinds`, that names the kinds the row claims. An attribute is no node, so it has its own list and the message
// `unlisted: The attribute is {spelling}.`
// A kind names the class of the node in clang: `GotoStmt`, `ImplicitCastExpr`, `FunctionDecl`, `BuiltinType`. The message is
// `{row}: The construct is {Kind}.` A kind that a row claims is that row's finding, even when it is on a list. A kind on no row and on
// no list is `unlisted`. Like the generic check, it reads the tree as the compiler has it, with the implicit casts.
class AllowlistCheck : public ClangTidyCheck {
public:
  AllowlistCheck(StringRef Name, ClangTidyContext *Context) : ClangTidyCheck(Name, Context), Ctx(Context) {}

  void registerMatchers(MatchFinder *Finder) override {
    const std::string Prefix = (getID() + ".").str();
    for (const auto &Option : Ctx->getOptions().CheckOptions) {
      StringRef Key = Option.getKey();
      if (!Key.consume_front(Prefix))
        continue;
      llvm::SmallVector<StringRef, 16> Kinds;
      StringRef(Option.getValue().Value).split(Kinds, ',', -1, false);
      for (StringRef Kind : Kinds) {
        Kind = Kind.trim();
        if (Kind.empty())
          continue;
        if (Key == "statements")
          Statements.insert(Kind);
        else if (Key == "declarations")
          Declarations.insert(Kind);
        else if (Key == "types")
          Types.insert(Kind);
        else if (Key == "attributes")
          Attributes.insert(Kind);
        else
          Claimed[Kind] = Key.str();
      }
    }
    // A node in a system header is no source of ours. The body of an implicit function comes from the compiler too, so none of its
    // statements is. Nor is a node below a substituted template argument: clang writes `(Enum)1` for an enum argument, and the
    // argument is judged where it is written. The test of the location comes first, because the headers hold most of the nodes.
    Finder->addMatcher(stmt(unless(isExpansionInSystemHeader()), unless(hasAncestor(functionDecl(isImplicit()))),
                            unless(hasAncestor(substNonTypeTemplateParmExpr())))
                           .bind("stmt"),
                       this);
    Finder->addMatcher(decl(unless(isExpansionInSystemHeader())).bind("decl"), this);
    Finder->addMatcher(typeLoc(unless(isExpansionInSystemHeader())).bind("type"), this);
  }

  void check(const MatchFinder::MatchResult &Result) override {
    SourceLocation Loc;
    std::string Kind;
    const llvm::StringSet<> *Allowed = nullptr;
    if (const auto *S = Result.Nodes.getNodeAs<Stmt>("stmt")) {
      if (const auto *Attributed = dyn_cast<AttributedStmt>(S))
        for (const Attr *A : Attributed->getAttrs())
          checkAttribute(A, *Result.SourceManager);
      Loc = S->getBeginLoc();
      Kind = S->getStmtClassName();
      Allowed = &Statements;
    } else if (const auto *D = Result.Nodes.getNodeAs<Decl>("decl")) {
      // The kinds of an implicit declaration come from the compiler, not from the source.
      if (D->isImplicit() || isa<TranslationUnitDecl>(D))
        return;
      for (const Attr *A : D->attrs())
        checkAttribute(A, *Result.SourceManager);
      Loc = D->getLocation();
      Kind = std::string(D->getDeclKindName()) + "Decl";
      Allowed = &Declarations;
    } else if (const auto *T = Result.Nodes.getNodeAs<TypeLoc>("type")) {
      if (T->isNull())
        return;
      Loc = T->getBeginLoc();
      Kind = std::string(T->getTypePtr()->getTypeClassName()) + "Type";
      Allowed = &Types;
      // A qualifier is no node kind and no attribute, and `__restrict` promises the compiler that two pointers never alias.
      if (T->getType().isLocalRestrictQualified() && Loc.isValid())
        diag(Result.SourceManager->getFileLoc(Loc), "unlisted: The construct is __restrict.");
    } else {
      return;
    }
    if (Loc.isInvalid())
      return;
    // A node from a macro is reported where the macro is used.
    Loc = Result.SourceManager->getFileLoc(Loc);
    const auto Row = Claimed.find(Kind);
    if (Row != Claimed.end())
      diag(Loc, "%0: The construct is %1.") << Row->second << Kind;
    else if (!Allowed->contains(Kind))
      diag(Loc, "unlisted: The construct is %0.") << Kind;
  }

private:
  ClangTidyContext *Ctx;
  llvm::StringSet<> Statements, Declarations, Types, Attributes;
  // The kind, and the row that claims it.
  llvm::StringMap<std::string> Claimed;

  // An attribute that the compiler added, or that a redeclaration inherited, is judged where it is written.
  void checkAttribute(const Attr *A, const SourceManager &SM) {
    if (A->isImplicit() || A->isInherited() || Attributes.contains(A->getSpelling()) || A->getLocation().isInvalid())
      return;
    diag(SM.getFileLoc(A->getLocation()), "unlisted: The attribute is %0.") << A->getSpelling();
  }
};

// ------------------------------------------------------------ unlisted state, decisions 0035 and 0036

// The two kinds of contract line the gate reads: `//@ modifies a, b` and `//@ reads a, b`. Every other line is ignored, but it shows
// that the function has a contract, and a contract with no `modifies` line says that the function changes no global.
struct Contract {
  std::vector<std::string> Modifies, Reads;
  bool Any = false;  // a `//@` line of any kind is there
};

// The contract lines of the function that starts at `First`: the contiguous lines above that line that start with `//@`. A
// `CPLUSP_...(...)` marker line does not end the block. Any other line does. The lines come from the source buffer, because `//@`
// is no doc comment and the AST has not got it.
Contract contractAbove(const SourceManager &SM, SourceLocation First) {
  Contract C;
  First = SM.getExpansionLoc(First);
  if (First.isInvalid())
    return C;
  const auto [File, Offset] = SM.getDecomposedLoc(First);
  bool Invalid = false;
  const StringRef Text = SM.getBufferData(File, &Invalid);
  if (Invalid)
    return C;
  size_t Start = Text.substr(0, Offset).rfind('\n');
  Start = Start == StringRef::npos ? 0 : Start + 1;
  while (Start > 0) {
    // The line above is the text from the newline before it up to the newline that ends it.
    const size_t End = Start - 1;
    size_t Begin = Text.substr(0, End).rfind('\n');
    Begin = Begin == StringRef::npos ? 0 : Begin + 1;
    StringRef Line = Text.slice(Begin, End).trim();
    Start = Begin;
    if (Line.starts_with("CPLUSP_"))
      continue;
    if (!Line.consume_front("//@"))
      break;
    C.Any = true;
    Line = Line.ltrim();
    std::vector<std::string> *Names = Line.consume_front("modifies") ? &C.Modifies : Line.consume_front("reads") ? &C.Reads : nullptr;
    if (!Names || (!Line.empty() && !isspace(static_cast<unsigned char>(Line.front()))))
      continue;
    llvm::SmallVector<StringRef, 8> Parts;
    Line.split(Parts, ',', -1, false);
    for (StringRef Name : Parts)
      if (!Name.trim().empty())
        Names->push_back(Name.trim().str());
  }
  return C;
}

// Where a function starts: its return type, or its name for a constructor. A function template starts at its `template`, and its
// lines sit above that, as in examples/templates.
SourceLocation firstTokenOf(const FunctionDecl *Function) {
  if (const FunctionTemplateDecl *Template = Function->getDescribedFunctionTemplate())
    return Template->getBeginLoc();
  return Function->getOuterLocStart();
}

// ponytail: one ceiling. A callee that has no lines in this translation unit adds nothing, so a callee in a header behind -isystem,
// a callee through a function pointer, a virtual call that an override answers, and a callee in another file add nothing, unless it
// has no body and no lines at all, which the gate refuses. Upgrade: a contract reader that runs on every file, and a record of the
// lines of every function.
Contract contractOf(const SourceManager &SM, const FunctionDecl *Function) {
  Contract C;
  if (const FunctionDecl *Pattern = Function->getTemplateInstantiationPattern())
    Function = Pattern;
  for (const FunctionDecl *Declaration : Function->redecls()) {
    // The compiler's own functions have no place in the source, and the place of an implicit member is its class.
    if (Declaration->isImplicit() || SM.isInSystemHeader(Declaration->getLocation()))
      continue;
    Contract One = contractAbove(SM, firstTokenOf(Declaration));
    C.Modifies.insert(C.Modifies.end(), One.Modifies.begin(), One.Modifies.end());
    C.Reads.insert(C.Reads.end(), One.Reads.begin(), One.Reads.end());
    C.Any |= One.Any;
  }
  return C;
}

// The function whose lines judge `Function`. A lambda has none of its own, so its call operator is judged against the function that
// the lambda is written in.
const FunctionDecl *linesOwner(const FunctionDecl *Function) {
  while (const auto *Method = dyn_cast<CXXMethodDecl>(Function)) {
    if (!Method->getParent()->isLambda())
      break;
    const auto *Outer = dyn_cast<FunctionDecl>(Method->getParent()->getDeclContext());
    if (!Outer)
      break;
    Function = Outer;
  }
  return Function;
}

// The name of a variable as a contract line writes it: qualified, and without the arguments of a class template, so `Box<int>::n` is
// `Box::n`.
std::string nameOf(const VarDecl *Var) {
  std::string Name;
  int Depth = 0;
  for (const char C : Var->getQualifiedNameAsString()) {
    if (C == '<')
      ++Depth;
    else if (C == '>' && Depth > 0)
      --Depth;
    else if (Depth == 0)
      Name += C;
  }
  return Name;
}

// A mutable global or a static data member. A constant, a member and a function-local static are not state here.
bool isState(const VarDecl *Var) { return isMutableGlobal(Var) && !Var->isStaticLocal(); }

// The state variable that a listed name names. A name is the qualified name of the variable, or that name after a `::`, and it names
// the variable only when no other state variable of the whole translation unit matches it too: two statics called `n` are named by
// none, and so are two that end in `C::k`.
const std::string *resolve(StringRef Listed, const std::vector<std::string> &State) {
  const std::string *Found = nullptr;
  for (const std::string &Name : State) {
    const StringRef Full = Name;
    if (Full == Listed || (Full.size() > Listed.size() && Full.ends_with(Listed) && Full.drop_back(Listed.size()).ends_with("::"))) {
      if (Found)
        return nullptr;
      Found = &Name;
    }
  }
  return Found;
}

// A function with a body in this translation unit, or whose pattern has one.
bool hasBody(const FunctionDecl *Function) {
  const FunctionDecl *Pattern = Function->getTemplateInstantiationPattern();
  return Function->isDefined() || (Pattern && Pattern->isDefined());
}

// A function that the gate cannot read: outside std and the system headers, with no body here and no contract lines. A call of it
// may change any global. A builtin, a function that the compiler or a `= default` defines, and a pure virtual function, which an
// override answers, are no such function.
// ponytail: an override in another file is not read, so a virtual call adds only what the declaration lists. Upgrade: read every
// override of the class hierarchy that the file can see.
bool isOpaque(const SourceManager &SM, const FunctionDecl *Function) {
  if (Function->isImplicit() || Function->isDefaulted() || Function->isPureVirtual() || Function->getBuiltinID() || inStdNamespace(Function) ||
      SM.isInSystemHeader(Function->getLocation()) || hasBody(Function))
    return false;
  return !contractOf(SM, Function).Any;
}

// A constructor or destructor that nobody wrote, so its lines are those of what it runs.
bool isImplicitMember(const CXXMethodDecl *Method) { return Method->isImplicit() || (Method->isDefaulted() && !Method->isUserProvided()); }

bool inSystemHeader(const CXXRecordDecl *Record) { return Record->getASTContext().getSourceManager().isInSystemHeader(Record->getLocation()); }

const CXXRecordDecl *classOf(QualType Type) {
  const CXXRecordDecl *Record = Type->getBaseElementTypeUnsafe()->getAsCXXRecordDecl();
  return Record ? Record->getDefinition() : nullptr;
}

// A walk over the bases and the members of a class goes to the end of them. A class holds its members by value, so the graph is finite,
// and the set keeps a class that appears twice from being walked twice. No limit ends a walk in a pass, decision 0036.
using ClassSet = llvm::SmallPtrSet<const CXXRecordDecl *, 16>;

// The constructor of `Class` that is of the same kind as `Kind`, or null when the class declares none: an implicit one runs then. A
// move that the class does not declare runs the copy.
const CXXConstructorDecl *constructorLike(const CXXRecordDecl *Class, const CXXConstructorDecl *Kind) {
  const auto Find = [&](bool (CXXConstructorDecl::*Is)() const) -> const CXXConstructorDecl * {
    for (const CXXConstructorDecl *Constructor : Class->ctors())
      if ((Constructor->*Is)())
        return Constructor;
    return nullptr;
  };
  if (Kind->isDefaultConstructor())
    return Find(&CXXConstructorDecl::isDefaultConstructor);
  const CXXConstructorDecl *Copy = Find(&CXXConstructorDecl::isCopyConstructor);
  if (Kind->isCopyConstructor())
    return Copy;
  const CXXConstructorDecl *Move = Find(&CXXConstructorDecl::isMoveConstructor);
  return Move ? Move : Copy;
}

// The expressions of the in-class initializers that an implicit default constructor of `Record` runs, for its members and its bases.
// ponytail: this walk and the two below go over the same bases and members. Upgrade: one walk that takes what to collect.
void inClassInitializers(const CXXRecordDecl *Record, const CXXConstructorDecl *Kind, ClassSet &Seen, llvm::SmallVectorImpl<const Expr *> &Out) {
  if (!Record || inSystemHeader(Record) || !Seen.insert(Record).second)
    return;
  const auto Member = [&](QualType Type, const Expr *Init) {
    if (Init) {
      Out.push_back(Init);
      return;
    }
    const CXXRecordDecl *Class = classOf(Type);
    const CXXConstructorDecl *Constructor = Class ? constructorLike(Class, Kind) : nullptr;
    if (Class && (!Constructor || isImplicitMember(Constructor)))
      inClassInitializers(Class, Kind, Seen, Out);
  };
  for (const CXXBaseSpecifier &Base : Record->bases())
    Member(Base.getType(), nullptr);
  for (const FieldDecl *Field : Record->fields())
    Member(Field->getType(), Field->getInClassInitializer());
}

// The user-written constructors that an implicit constructor of `Record` runs for its bases and members, of the kind it is.
void constructorsRunBy(const CXXRecordDecl *Record, const CXXConstructorDecl *Kind, ClassSet &Seen,
                       llvm::SmallVectorImpl<const FunctionDecl *> &Out) {
  if (!Record || inSystemHeader(Record) || !Seen.insert(Record).second)
    return;
  const auto Member = [&](QualType Type, bool HasInit) {
    const CXXRecordDecl *Class = classOf(Type);
    if (!Class || (Kind->isDefaultConstructor() && HasInit))
      return;
    const CXXConstructorDecl *Constructor = constructorLike(Class, Kind);
    if (!Constructor || isImplicitMember(Constructor))
      constructorsRunBy(Class, Kind, Seen, Out);
    else
      Out.push_back(Constructor);
  };
  for (const CXXBaseSpecifier &Base : Record->bases())
    Member(Base.getType(), false);
  for (const FieldDecl *Field : Record->fields())
    Member(Field->getType(), Field->hasInClassInitializer());
}

// The user classes among the template arguments of `Type`, and among its own parts: what a std template over them runs the code of.
// A reference and an array are looked through. A pointer holds no object, so it runs nothing.
using TypeSet = llvm::SmallPtrSet<const void *, 16>;
void userClassesIn(QualType Type, ClassSet &Out, TypeSet &Seen);

void userClassesInArgs(llvm::ArrayRef<TemplateArgument> Args, ClassSet &Out, TypeSet &Seen) {
  for (const TemplateArgument &Arg : Args) {
    if (Arg.getKind() == TemplateArgument::Type)
      userClassesIn(Arg.getAsType(), Out, Seen);
    else if (Arg.getKind() == TemplateArgument::Pack)
      userClassesInArgs(Arg.pack_elements(), Out, Seen);
  }
}

void userClassesIn(QualType Type, ClassSet &Out, TypeSet &Seen) {
  if (Type.isNull())
    return;
  const clang::Type *Base = Type.getNonReferenceType()->getBaseElementTypeUnsafe();
  if (!Seen.insert(Base->getCanonicalTypeInternal().getAsOpaquePtr()).second)
    return;
  const CXXRecordDecl *Record = Base->getAsCXXRecordDecl();
  if (!Record)
    return;
  if (const CXXRecordDecl *Definition = Record->getDefinition())
    Record = Definition;
  if (!inSystemHeader(Record))
    Out.insert(Record);
  if (const auto *Specialization = dyn_cast<ClassTemplateSpecializationDecl>(Record))
    userClassesInArgs(Specialization->getTemplateArgs().asArray(), Out, Seen);
}

// The user-written destructors that destroying an object of `Record` runs: its own, and those of its bases and members. A member that
// is a std template over a user class runs that class's destructor too.
void destructorsRunBy(const CXXRecordDecl *Record, ClassSet &Seen, llvm::SmallVectorImpl<const FunctionDecl *> &Out) {
  if (!Record || inSystemHeader(Record) || !Seen.insert(Record).second)
    return;
  const CXXDestructorDecl *Destructor = Record->getDestructor();
  if (Destructor && !isImplicitMember(Destructor))
    Out.push_back(Destructor);
  const auto Part = [&](QualType Type) {
    const CXXRecordDecl *Class = classOf(Type);
    if (!Class)
      return;
    if (!inSystemHeader(Class)) {
      destructorsRunBy(Class, Seen, Out);
    } else if (const auto *Specialization = dyn_cast<ClassTemplateSpecializationDecl>(Class)) {
      ClassSet Users;
      TypeSet Types;
      userClassesInArgs(Specialization->getTemplateArgs().asArray(), Users, Types);
      for (const CXXRecordDecl *User : Users)
        destructorsRunBy(User, Seen, Out);
    }
  };
  for (const CXXBaseSpecifier &Base : Record->bases())
    Part(Base.getType());
  for (const FieldDecl *Field : Record->fields())
    Part(Field->getType());
}

// The functions of a user class that a std template may run: its constructors, its destructor and its assignment operators, with a
// constructor that nobody wrote replaced by the constructors it runs.
void classFunctions(const CXXRecordDecl *Class, llvm::SmallVectorImpl<const FunctionDecl *> &Out) {
  for (const CXXConstructorDecl *Constructor : Class->ctors()) {
    if (!isImplicitMember(Constructor)) {
      Out.push_back(Constructor);
    } else if (Constructor->isDefaultConstructor() || Constructor->isCopyOrMoveConstructor()) {
      ClassSet Seen;
      constructorsRunBy(Class, Constructor, Seen, Out);
    }
  }
  ClassSet Seen;
  destructorsRunBy(Class, Seen, Out);
  for (const CXXMethodDecl *Method : Class->methods())
    if ((Method->isCopyAssignmentOperator() || Method->isMoveAssignmentOperator()) && !isImplicitMember(Method))
      Out.push_back(Method);
}

// The user classes that a call of `Callee` runs the code of when `Callee` is a template specialization declared in a system header: the
// classes among its template arguments, and among the types of the arguments it is given. A std function that is no template runs none.
void stdTemplateUsers(const FunctionDecl *Callee, const SourceManager &SM, llvm::ArrayRef<const Expr *> Args, ClassSet &Out) {
  if (!Callee || !SM.isInSystemHeader(Callee->getLocation()))
    return;
  TypeSet Types;
  bool Template = false;
  if (const TemplateArgumentList *List = Callee->getTemplateSpecializationArgs()) {
    userClassesInArgs(List->asArray(), Out, Types);
    Template = true;
  }
  if (const auto *Method = dyn_cast<CXXMethodDecl>(Callee))
    if (const auto *Specialization = dyn_cast<ClassTemplateSpecializationDecl>(Method->getParent())) {
      userClassesInArgs(Specialization->getTemplateArgs().asArray(), Out, Types);
      Template = true;
    }
  if (!Template)
    return;
  for (const Expr *Arg : Args)
    userClassesIn(Arg->getType(), Out, Types);
}

// Calls Visit on every node the function runs: the nodes of a lambda body too, because the lambda runs inside the function that passes
// it. An unevaluated operand is not run. A default argument runs at the call, so its nodes are reported at the call, and `Where` is
// where to report, or invalid for the node's own place. A default member initializer runs where the object is made, in an
// initializer list or in an implicit constructor, and its nodes stay where they are written.
template <typename F> void walkNodes(const Stmt *S, SourceLocation Call, SourceLocation Where, const F &Visit) {
  if (!S || isa<UnaryExprOrTypeTraitExpr, CXXNoexceptExpr, CXXTypeidExpr>(S))
    return;
  if (const auto *Default = dyn_cast<CXXDefaultArgExpr>(S)) {
    walkNodes(Default->getExpr(), Call, Call, Visit);
    return;
  }
  if (const auto *Init = dyn_cast<CXXDefaultInitExpr>(S)) {
    walkNodes(Init->getExpr(), Call, Where, Visit);
    return;
  }
  Visit(S, Where);
  if (isa<CallExpr, CXXConstructExpr>(S))
    Call = S->getBeginLoc();
  for (const Stmt *Child : S->children())
    walkNodes(Child, Call, Where, Visit);
  if (const auto *Construct = dyn_cast<CXXConstructExpr>(S)) {
    const CXXConstructorDecl *Constructor = Construct->getConstructor();
    if (Constructor->isDefaultConstructor() && isImplicitMember(Constructor)) {
      llvm::SmallVector<const Expr *, 4> Inits;
      ClassSet Seen;
      inClassInitializers(Constructor->getParent(), Constructor, Seen, Inits);
      for (const Expr *Init : Inits)
        walkNodes(Init, Call, Where, Visit);
    }
  }
}

// Calls Each on the root path of everything that S writes: an assignment target, an increment, an argument that binds to a non-const
// reference, pointer or span, and the object of a non-const member call.
template <typename F> void forEachWrite(const Stmt *S, const F &Each) {
  if (const auto *Binary = dyn_cast<BinaryOperator>(S); Binary && Binary->isAssignmentOp()) {
    for (const RootPath &Path : rootsOf(Binary->getLHS()).Paths)
      Each(Path);
  } else if (const auto *Unary = dyn_cast<UnaryOperator>(S); Unary && Unary->isIncrementDecrementOp()) {
    for (const RootPath &Path : rootsOf(Unary->getSubExpr()).Paths)
      Each(Path);
  } else if (isa<CallExpr, CXXConstructExpr>(S)) {
    llvm::SmallVector<Arg, 4> Args;
    collectArgs(cast<Expr>(S), Args);
    for (const Arg &A : Args)
      if (A.Writes)
        for (const RootPath &Path : A.Where.Paths)
          Each(Path);
  }
}

// What a call of a function may change, found once per function in a translation unit.
llvm::DenseMap<const FunctionDecl *, bool> &reachCache() {
  static llvm::DenseMap<const FunctionDecl *, bool> Cache;
  return Cache;
}

void resetReach() { reachCache().clear(); }

// The call graph from `Function`, to the end: a function that lists a global on its `modifies` line, that writes a mutable global, or that
// the gate cannot read, may change a global, and so does every function that calls it. The lines of the visited functions are read as
// the state check reads them.
bool reachesState(const FunctionDecl *Function) {
  auto &Cache = reachCache();
  if (const auto Known = Cache.find(Function); Known != Cache.end())
    return Known->second;
  llvm::SmallPtrSet<const FunctionDecl *, 16> Seen;
  llvm::SmallVector<const FunctionDecl *, 8> Work{Function};
  bool Found = false;
  while (!Work.empty() && !Found) {
    const FunctionDecl *Current = Work.pop_back_val();
    if (!Seen.insert(Current->getCanonicalDecl()).second)
      continue;
    const SourceManager &SM = Current->getASTContext().getSourceManager();
    if (inStdNamespace(Current) || SM.isInSystemHeader(Current->getLocation()))
      continue;
    if (isOpaque(SM, Current) || !contractOf(SM, Current).Modifies.empty()) {
      Found = true;
      break;
    }
    const FunctionDecl *Definition = nullptr;
    Current->isDefined(Definition);
    if (!Definition && Current->getTemplateInstantiationPattern())
      Current->getTemplateInstantiationPattern()->isDefined(Definition);
    if (!Definition || !Definition->getBody())
      continue;
    llvm::SmallVector<const Stmt *, 4> Parts{Definition->getBody()};
    if (const auto *Constructor = dyn_cast<CXXConstructorDecl>(Definition))
      for (const CXXCtorInitializer *Init : Constructor->inits())
        Parts.push_back(Init->getInit());
    for (const Stmt *Part : Parts)
      walkNodes(Part, SourceLocation(), SourceLocation(), [&](const Stmt *S, SourceLocation) {
        forEachWrite(S, [&](const RootPath &Path) { Found |= Path.Global; });
        if (const auto *Call = dyn_cast<CallExpr>(S); Call && Call->getDirectCallee())
          Work.push_back(Call->getDirectCallee());
        else if (const auto *Construct = dyn_cast<CXXConstructExpr>(S))
          Work.push_back(Construct->getConstructor());
      });
  }
  Cache[Function] = Found;
  return Found;
}

// cplusp-unlisted-state: decisions 0035 and 0036. A function writes only the global state its `//@ modifies` line lists, and reads only
// what its `//@ reads` or `modifies` line lists. State is a mutable global or static data member that a system header does not declare.
// A write is an assignment target, an increment, the object of a non-const member call, or a binding to a non-const reference, pointer
// or span. Any other mention is a read. A call adds what its callee lists. So do the constructors an implicit constructor runs, the
// destructor of every local, temporary and deleted object, a function passed by name, and the user classes that a std template runs.
// A call of a function that the gate cannot read is refused, and so is a reference from a function this file does not define: any
// global may be behind it, and no line can list that. The message is `global_state: {sentence}`, one finding per access.
// It reads the tree as the compiler has it, with the instantiations of a template, so a call that depends on a template argument has
// its callee. The pattern is not judged.
class UnlistedStateCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void onStartOfTranslationUnit() override {
    StateNames.clear();
    Collected = false;
    resetReach();
  }
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(functionDecl(isDefinition(), unless(isExpansionInSystemHeader()), unless(notJudged())).bind("function"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    const auto *Function = Result.Nodes.getNodeAs<FunctionDecl>("function");
    const SourceManager &SM = *Result.SourceManager;
    if (!Collected) {
      collectState(Result.Context->getTranslationUnitDecl(), SM, StateNames);
      llvm::sort(StateNames);
      StateNames.erase(std::unique(StateNames.begin(), StateNames.end()), StateNames.end());
      Collected = true;
    }
    // The nodes the function runs: its body, and the initializers of a constructor.
    llvm::SmallVector<const Stmt *, 4> Parts;
    Parts.push_back(Function->getBody());
    if (const auto *Constructor = dyn_cast<CXXConstructorDecl>(Function))
      for (const CXXCtorInitializer *Init : Constructor->inits())
        Parts.push_back(Init->getInit());
    // First the writes, because a loop variable writes a variable that the range names, and the range comes first in the tree.
    llvm::SmallPtrSet<const Stmt *, 16> Written;
    for (const Stmt *Part : Parts)
      walkNodes(Part, SourceLocation(), SourceLocation(), [&](const Stmt *S, SourceLocation) {
        forEachWrite(S, [&](const RootPath &Path) {
          if (Path.At)
            Written.insert(Path.At);
        });
      });
    // A reference from a function this file does not define is refused where the function reaches through it: a write, a read of
    // the value, a dereference, and any argument or object that a call is given, const or not.
    llvm::SmallPtrSet<const CallExpr *, 4> Reached;
    for (const Stmt *W : Written)
      if (const auto *Call = dyn_cast<CallExpr>(W))
        Reached.insert(Call);
    // The lines may sit on an earlier declaration, as a header has them, and not on the definition. A lambda has none of its own.
    const FunctionDecl *Owner = linesOwner(Function);
    const Contract Own = contractOf(SM, Owner);
    std::set<std::string> Modifies, Listed;
    for (const std::string &Name : Own.Modifies)
      if (const std::string *Var = resolve(Name, StateNames)) {
        Modifies.insert(*Var);
        Listed.insert(*Var);
      }
    for (const std::string &Name : Own.Reads)
      if (const std::string *Var = resolve(Name, StateNames))
        Listed.insert(*Var);
    const auto Refuse = [&](SourceLocation Loc, const std::string &Var, bool Write) {
      if ((Write ? Modifies : Listed).count(Var))
        return;
      if (Write)
        diag(SM.getExpansionLoc(Loc), "global_state: %0 changes, and the modifies line does not list it.") << StringRef(Var);
      else
        diag(SM.getExpansionLoc(Loc), "global_state: %0 is read, and no reads or modifies line lists it.") << StringRef(Var);
    };
    // What a callee lists, at `Loc`. A name on its lines that matches a state variable is state, whatever the callee calls its
    // parameters.
    const auto Bring = [&](const FunctionDecl *Callee, SourceLocation Loc) {
      const Contract Brought = contractOf(SM, Callee);
      for (const std::string &Name : Brought.Modifies)
        if (const std::string *Var = resolve(Name, StateNames))
          Refuse(Loc, *Var, true);
      for (const std::string &Name : Brought.Reads)
        if (const std::string *Var = resolve(Name, StateNames))
          Refuse(Loc, *Var, false);
    };
    // What an object of this type runs when it is made or destroyed: the destructors of a user class, and everything that a std
    // template over user classes runs of them.
    const auto BringType = [&](QualType Type, SourceLocation Loc) {
      const CXXRecordDecl *Class = classOf(Type);
      if (!Class)
        return;
      llvm::SmallVector<const FunctionDecl *, 8> Run;
      if (!inSystemHeader(Class)) {
        ClassSet Seen;
        destructorsRunBy(Class, Seen, Run);
      } else if (const auto *Specialization = dyn_cast<ClassTemplateSpecializationDecl>(Class)) {
        ClassSet Users;
        TypeSet Types;
        userClassesInArgs(Specialization->getTemplateArgs().asArray(), Users, Types);
        for (const CXXRecordDecl *User : Users)
          classFunctions(User, Run);
      }
      for (const FunctionDecl *Function : Run)
        Bring(Function, Loc);
    };
    // The callee of a call is no function passed by name.
    llvm::SmallPtrSet<const Expr *, 16> CalleeRefs;
    for (const Stmt *Part : Parts)
      walkNodes(Part, SourceLocation(), SourceLocation(), [&](const Stmt *S, SourceLocation Where) {
        const SourceLocation Here = Where.isValid() ? Where : S->getBeginLoc();
        const VarDecl *Var = nullptr;
        if (const auto *Ref = dyn_cast<DeclRefExpr>(S))
          Var = dyn_cast<VarDecl>(Ref->getDecl());
        else if (const auto *Member = dyn_cast<MemberExpr>(S))
          Var = dyn_cast<VarDecl>(Member->getMemberDecl());
        if (Var && isState(Var))
          Refuse(Here, nameOf(Var), Written.contains(S));
        // A function passed by name runs where the callee runs it, so its lines count here.
        if (const auto *Ref = dyn_cast<DeclRefExpr>(S))
          if (const auto *Named = dyn_cast<FunctionDecl>(Ref->getDecl()); Named && !CalleeRefs.contains(Ref))
            Bring(Named, Here);
        const Expr *Through = nullptr;
        if (const auto *Cast = dyn_cast<ImplicitCastExpr>(S); Cast && Cast->getCastKind() == CK_LValueToRValue)
          Through = Cast->getSubExpr();
        else if (const auto *Unary = dyn_cast<UnaryOperator>(S); Unary && Unary->getOpcode() == UO_Deref)
          Through = Unary->getSubExpr();
        else if (const auto *Subscript = dyn_cast<ArraySubscriptExpr>(S))
          Through = Subscript->getBase();
        else if (const auto *Arrow = dyn_cast<MemberExpr>(S); Arrow && Arrow->isArrow())
          Through = Arrow->getBase();
        if (Through)
          for (const RootPath &Path : rootsOf(Through).Paths)
            if (const auto *Call = dyn_cast_or_null<CallExpr>(Path.At); Call && Path.Steps[0] == &StateKey)
              Reached.insert(Call);
        // A local lives to the end of its scope, and a temporary to the end of its full expression. Each runs its destructor.
        if (const auto *Declared = dyn_cast<DeclStmt>(S)) {
          for (const Decl *D : Declared->decls())
            if (const auto *Local = dyn_cast<VarDecl>(D); Local && Local->hasLocalStorage() && !Local->getType()->isReferenceType() && !Local->isImplicit())
              BringType(Local->getType(), Local->getLocation());
        } else if (const auto *Temporary = dyn_cast<CXXBindTemporaryExpr>(S)) {
          BringType(Temporary->getType(), Here);
        } else if (const auto *Delete = dyn_cast<CXXDeleteExpr>(S)) {
          // delete runs the destructor of the deleted type.
          BringType(Delete->getDestroyedType(), Here);
        }
        const FunctionDecl *Callee = nullptr;
        llvm::SmallVector<const Expr *, 4> Arguments;
        if (const auto *Call = dyn_cast<CallExpr>(S)) {
          Callee = Call->getDirectCallee();
          Arguments.assign(Call->arg_begin(), Call->arg_end());
          CalleeRefs.insert(Call->getCallee()->IgnoreParenImpCasts());
        } else if (const auto *Construct = dyn_cast<CXXConstructExpr>(S)) {
          const CXXConstructorDecl *Constructor = Construct->getConstructor();
          Callee = Constructor;
          Arguments.assign(Construct->arg_begin(), Construct->arg_end());
          // An implicit constructor runs the constructors of its bases and members.
          if (isImplicitMember(Constructor) && (Constructor->isDefaultConstructor() || Constructor->isCopyOrMoveConstructor())) {
            llvm::SmallVector<const FunctionDecl *, 4> Run;
            ClassSet Seen;
            constructorsRunBy(Constructor->getParent(), Constructor, Seen, Run);
            for (const FunctionDecl *Constructed : Run)
              Bring(Constructed, Here);
          }
        }
        if (isa<CallExpr, CXXConstructExpr>(S)) {
          llvm::SmallVector<Arg, 4> Args;
          collectArgs(cast<Expr>(S), Args);
          for (const Arg &A : Args)
            for (const RootPath &Path : A.Where.Paths)
              if (const auto *Call = dyn_cast_or_null<CallExpr>(Path.At); Call && Path.Steps[0] == &StateKey)
                Reached.insert(Call);
        }
        if (!Callee)
          return;
        Bring(Callee, Here);
        // A std template over a user class runs the class's own functions.
        ClassSet Users;
        stdTemplateUsers(Callee, SM, Arguments, Users);
        for (const CXXRecordDecl *User : Users) {
          llvm::SmallVector<const FunctionDecl *, 8> Run;
          classFunctions(User, Run);
          for (const FunctionDecl *Member : Run)
            Bring(Member, Here);
        }
        if (isOpaque(SM, Callee) && !(isa<CallExpr>(S) && namedInStd(cast<CallExpr>(S), Callee)))
          diag(SM.getExpansionLoc(Here), "global_state: %0 has no body here and no contract lines, so it may change any global.")
              << StringRef(Callee->getNameAsString());
      });
    for (const CallExpr *Call : Reached)
      diag(SM.getExpansionLoc(Call->getBeginLoc()), "global_state: a reference from %0 may reach any global, and no line can list it.")
          << StringRef(Call->getDirectCallee()->getNameAsString());
  }

private:
  // The qualified names of the state of this file, found once per translation unit.
  std::vector<std::string> StateNames;
  bool Collected = false;

  // The state a file declares, outside the system headers: in a namespace, a linkage specification, a class or a class template.
  static void collectState(const DeclContext *Context, const SourceManager &SM, std::vector<std::string> &Out) {
    for (const Decl *D : Context->decls()) {
      if (SM.isInSystemHeader(D->getLocation()))
        continue;
      if (const auto *Var = dyn_cast<VarDecl>(D)) {
        if (isState(Var))
          Out.push_back(nameOf(Var));
      } else if (const auto *Template = dyn_cast<ClassTemplateDecl>(D)) {
        collectState(Template->getTemplatedDecl(), SM, Out);
      } else if (const auto *Template = dyn_cast<VarTemplateDecl>(D)) {
        if (isState(Template->getTemplatedDecl()))
          Out.push_back(nameOf(Template->getTemplatedDecl()));
      } else if (isa<NamespaceDecl, LinkageSpecDecl, CXXRecordDecl>(D)) {
        collectState(cast<DeclContext>(D), SM, Out);
      }
    }
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
    Factories.registerCheck<AllowlistCheck>("cplusp-allowlist");
    Factories.registerCheck<UnlistedStateCheck>("cplusp-unlisted-state");
    Factories.registerCheck<InexactLiteralCheck>("cplusp-inexact-literal");
  }
};

} // namespace

static clang::tidy::ClangTidyModuleRegistry::Add<CplusPModule> X("cplusp-module", "Adds the checks of cplusp.");

// Forces a linker to keep this module when it is linked in. A loaded plugin does not need it.
volatile int CplusPModuleAnchorSource = 0;
