// The clang-tidy plugin of cplusp. See docs/policy.md.
//
// One generic check, driven by the policy file.
// The gate writes each `matcher` entry of a rule as an option of the check, named `{rule_id}/{n}`.
// The check compiles the pattern and reports every match with the rule id as its message.
// The Rust side turns the rule id into the message for the bot.
//
// Twelve hand-written checks, for the rules that a pattern cannot say. The gate maps a finding to its rule by
// the name of the check, so their messages are short and plain. The sample pair of each rule is the evidence.

#include "ClangTidyCheck.h"
#include "ClangTidyModule.h"
#include "ClangTidyModuleRegistry.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/Dynamic/Diagnostics.h"
#include "clang/ASTMatchers/Dynamic/Parser.h"
#include "clang/AST/ASTLambda.h"
#include "clang/AST/GlobalDecl.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/RecordLayout.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Basic/CodeGenOptions.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/DiagnosticOptions.h"
#include "clang/Basic/SourceManagerInternals.h"
#include "clang/CodeGen/ModuleBuilder.h"
#include "clang/Lex/HeaderSearchOptions.h"
#include "clang/Lex/PPCallbacks.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Lex/PreprocessorOptions.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/Path.h"
#include "llvm/Transforms/Scalar/SROA.h"
#include "clang/Lex/Lexer.h"
#include "clang/Serialization/ASTReader.h"
#include "clang/Serialization/ModuleManager.h"

#include <cmath>
#include <algorithm>
#include <initializer_list>
#include <map>
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
// pattern relies on that: it matches the cast the compiler adds. Of the hand-written checks below, only three read the
// tree as spelled in the source: mutable, inexact-literal and lambda-limits, through SpelledCheck. The others see the full tree.
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
  // A dependent base has no record yet, so it counts as no base. The check visits every instantiation, decision 0055,
  // where `template <class T> struct X : Concrete, Holder<T>` has its bases.
  return llvm::all_of(Record->bases(), [](const CXXBaseSpecifier &Base) {
    const CXXRecordDecl *Parent = Base.getType()->getAsCXXRecordDecl();
    return !Parent || isPureInterface(Parent);
  });
}

// cplusp-multiple-inheritance: more than one direct base that is not a pure interface. It reads the bases the compiler resolves,
// so it visits template instantiations, decision 0055. An instantiation reports at the place in the pattern.
class MultipleInheritanceCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
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

// A type the holder can write through, decision 0055: a non-const lvalue or rvalue reference, a pointer to non-const, or a
// std::span of non-const elements, which writes through like a pointer. An rvalue reference writes too: `f(std::move(a),
// std::move(a))` moves one object twice. A forwarding reference has its instantiated type here, so it counts when it is non-const.
bool isMutableType(QualType Type) {
  Type = Type.getCanonicalType();
  if (const auto *Span = asSpan(Type))
    return !Span->getTemplateArgs()[0].getAsType().isConstQualified();
  return (Type->isReferenceType() || Type->isPointerType()) && !Type->getPointeeType().isConstQualified();
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
// It reads parameter types, so it judges each instantiation, decision 0055. An instantiation reports at the place in the pattern.
// The dependent pattern is judged by its spelling only: the kind of operator and the object, not the parameter types, which are
// not known there. So an operator in a template that nothing instantiates still stands, and one that both make is one finding. The call operator of a closure is no operator the author wrote: the check of lambdas judges it.
class ImpureOperatorCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(
        functionDecl(isOperatorFunction(), unless(isImplicit()), unless(isDefaulted()), unless(isDeleted()),
                     unless(cxxMethodDecl(ofClass(cxxRecordDecl(isLambda()))))).bind("operator"),
        this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    const auto *Function = Result.Nodes.getNodeAs<FunctionDecl>("operator");
    const auto *Method = dyn_cast<CXXMethodDecl>(Function);
    const bool Impure = Function->isTemplated() ? isAssignmentOrIncrement(Function->getOverloadedOperator()) || (Method && !Method->isStatic() && !Method->isConst())
                                                : isImpureOperator(Function);
    if (Impure)
      diag(Function->getLocation(), "operator is not pure");
  }
};

// ponytail: a name test. The `__wrap_iter` of libc++ passes, and so does a pointer iterator, as in std::array,
// unless a begin call stores it. The upgrade is a list of the library's iterator types, or a test of iterator_category.
AST_MATCHER(ValueDecl, hasIteratorType) {
  const CXXRecordDecl *Record = Node.getType().getNonReferenceType()->getAsCXXRecordDecl();
  return Record && Record->getName().contains("iterator");
}

// cplusp-iterator-arithmetic: (a) begin or end that is not a direct argument of a std call,
// (b) std::next, prev, advance and distance, (c) a variable, parameter or field of an iterator type.
// It reads types the compiler resolves, so it visits template instantiations, decision 0055: `auto it = c.begin()` in a template
// body has an iterator type only in an instantiation, and the finding stands at the place in the pattern. The traversal sees the
// implicit nodes too, so the matchers leave out the begin and end of a range-for and the fields of a closure, and match a call
// by its spelled parents.
class IteratorArithmeticCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void registerMatchers(MatchFinder *Finder) override {
    const auto Bounds = anyOf(callee(cxxMethodDecl(hasAnyName("begin", "end", "cbegin", "cend", "rbegin", "rend", "crbegin", "crend"))),
                              callee(functionDecl(hasAnyName("::std::begin", "::std::end", "::std::cbegin", "::std::cend", "::std::rbegin",
                                                             "::std::rend", "::std::crbegin", "::std::crend"))));
    Finder->addMatcher(callExpr(unless(hasParent(varDecl(isImplicit()))),
                                traverse(TK_IgnoreUnlessSpelledInSource, callExpr(Bounds, unless(hasParent(stdCall())))))
                           .bind("call"),
                       this);
    Finder->addMatcher(callExpr(callee(functionDecl(hasAnyName("::std::next", "::std::prev", "::std::advance", "::std::distance")))).bind("call"), this);
    Finder->addMatcher(valueDecl(anyOf(varDecl(), fieldDecl()), hasIteratorType(), unless(isImplicit())).bind("decl"), this);
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

// `std::as_const` is a cast to const.
bool isAsConst(const FunctionDecl *Function) {
  return Function && inStdNamespace(Function) && Function->getDeclName().isIdentifier() && Function->getName() == "as_const";
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

// The type of the object of a member call, looked at through a pointer. The object of `p->get()` is the pointer that `p->` returns.
QualType objectType(const Expr *Object) {
  const QualType Type = Object->IgnoreParenImpCasts()->getType();
  return Type->isPointerType() ? Type->getPointeeType() : Type;
}

// A call that reaches through an owner, a unique_ptr or shared_ptr: its `operator*`, `operator->`, `get`, or the subscript of an array owner.
// The operator of a shared_ptr is a member of its base, so the object is cast. The type of the owner is under the cast.
// `std::to_address` of an owner is no access here. The row `containers` bans it.
bool isOwnerAccess(const CallExpr *Call) {
  const FunctionDecl *Function = Call->getDirectCallee();
  const Expr *Object = Function ? objectOf(Call) : nullptr;
  if (!Object || !isOwner(objectType(Object)))
    return false;
  const OverloadedOperatorKind Operator = Function->getOverloadedOperator();
  return Operator == OO_Star || Operator == OO_Arrow || Operator == OO_Subscript ||
         (Function->getDeclName().isIdentifier() && Function->getName() == "get");
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
    // The roots are those of the object or the first argument. The handle that the call reaches through is the call's own to say.
    Walk W = objectOf(Call) ? rootsOf(objectOf(Call)) : Call->getNumArgs() ? rootsOf(Call->getArg(0)) : Walk();
    W.ConstHandle |= rootsOf(Init).ConstHandle;
    return W;
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
  const bool Deref = Object && isHandle(objectType(Object)) && (Operator == OO_Star || Operator == OO_Arrow);
  if (Object && (Deref || Operator == OO_Subscript || keepsRoot(Function))) {
    W = rootsOf(Object);
    // The owner is const as declared, not as the implicit cast to the const operator makes it. A write through `get()` or
    // through the subscript of an array owner is as much a write through the handle as one through `*`.
    if (isOwnerAccess(Call) && objectType(Object).isConstQualified())
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
  bool ReadOnly = false;
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
    // A span of const elements reads what it is made from, though the library takes a non-const reference to make it.
    ReadOnly = asSpan(Construct->getType()) && !isMutableType(Construct->getType());
  }
  if (!Function)
    return;
  for (unsigned I = 0; I < Args.size() && I < Function->getNumParams(); ++I) {
    const QualType Type = Function->getParamDecl(I)->getType();
    if (bindsToName(Type))
      Out.push_back({rootsOf(Args[I]), isMutableType(Type) && !ReadOnly, false,
                     Type->isReferenceType() && Type->getPointeeType().isConstQualified() && inStdNamespace(Function)});
  }
}

// A function that the semantic checks do not judge: the dependent pattern of a template, which is judged at each instantiation where
// every type and every callee is known, and the body of an implicit function, which the compiler wrote. A lambda's call operator is
// implicit and is judged, because the lambda runs where it is written. The state check reads it as a carrier, decision 0037.
// Decision 0036.
bool notJudgedFunction(const FunctionDecl &Node) {
  const auto *Method = dyn_cast<CXXMethodDecl>(&Node);
  return Node.isDependentContext() || (Node.isImplicit() && !(Method && Method->getParent()->isLambda()));
}

AST_MATCHER(FunctionDecl, notJudged) { return notJudgedFunction(Node); }

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

// A declaration of the library: it is in std, and in a system header. The place decides, not the namespace. A file may open `namespace std`.
bool inLibrary(const Decl *Declaration) {
  return inStdNamespace(Declaration) && Declaration->getASTContext().getSourceManager().isInSystemHeader(Declaration->getLocation());
}

// Whether a type carries a way to write, decisions 0041 and 0043. It reads what the type holds.
// A pointer or a reference to non-const carries one. To const, it carries what its pointee carries. A pointer to a function carries
// nothing. An array carries what its element carries. A record, of the file or of the library, template or not, carries what its fields
// and bases carry. A template of the library also carries what its type arguments carry.
// A container of the library that owns its elements on the heap counts by all its type arguments, decision 0044.
// They are the elements, the comparator, the hasher and the allocator. A copy of it copies each of them.
// So its own pointers are no second name for anything.
// Const reaches the fields, the bases, and the arguments of an owning container. A pointer member of a const record still carries,
// because const does not reach its pointee. A mutable field of a const record carries too, whatever its type.
// A const unique_ptr carries nothing, decision 0042. It cannot be copied, and every use of what it owns is judged as a source of its own.
// A type that the check cannot see whole carries a way to write. An incomplete record is one.
// `Seen` holds the types under judgement, with their qualifiers, and stops a record that holds itself.
using SeenTypes = llvm::SmallDenseSet<QualType, 8>;

bool carriesWrite(QualType Type, SeenTypes &Seen);

bool argumentsCarryWrite(ArrayRef<TemplateArgument> Args, bool Const, SeenTypes &Seen) {
  return llvm::any_of(Args, [&](const TemplateArgument &A) {
    return A.getKind() == TemplateArgument::Pack ? argumentsCarryWrite(A.pack_elements(), Const, Seen)
                                                 : A.getKind() == TemplateArgument::Type &&
                                                       carriesWrite(Const ? A.getAsType().withConst() : A.getAsType(), Seen);
  });
}

bool carriesWrite(QualType Type, SeenTypes &Seen) {
  Type = Type.getCanonicalType();
  if (Type->isPointerType() || Type->isReferenceType()) {
    const QualType Pointee = Type->getPointeeType();
    return !Pointee->isFunctionType() && (!Pointee.isConstQualified() || carriesWrite(Pointee, Seen));
  }
  const bool Const = Type.isConstQualified();
  const auto Held = [&](QualType Member, bool Mutable = false) { return carriesWrite(Const && !Mutable ? Member.withConst() : Member, Seen); };
  if (const auto *Array = Type->getAsArrayTypeUnsafe())
    return Held(Array->getElementType());
  const CXXRecordDecl *Record = Type->getAsCXXRecordDecl();
  if (!Record)
    return false;
  const bool Library = inLibrary(Record), Named = Record->getDeclName().isIdentifier();
  if (Library && Const && Named && Record->getName() == "unique_ptr")
    return false;
  if (!Record->hasDefinition())
    return true;
  if (!Seen.insert(Type).second)
    return false;
  const auto *Spec = dyn_cast<ClassTemplateSpecializationDecl>(Record);
  if (Library && Spec && Named &&
      llvm::is_contained({"basic_string", "vector", "deque", "list", "forward_list", "map", "multimap", "set", "multiset", "unordered_map",
                          "unordered_multimap", "unordered_set", "unordered_multiset"},
                         Record->getName()))
    return argumentsCarryWrite(Spec->getTemplateArgs().asArray(), Const, Seen);
  return llvm::any_of(Record->bases(), [&](const CXXBaseSpecifier &Base) { return Held(Base.getType()); }) ||
         llvm::any_of(Record->fields(),
                      [&](const FieldDecl *Field) { return (Const && Field->isMutable()) || Held(Field->getType(), Field->isMutable()); }) ||
         (Library && Spec && argumentsCarryWrite(Spec->getTemplateArgs().asArray(), Const, Seen));
}

bool givesWrite(QualType Type) {
  SeenTypes Seen;
  return carriesWrite(Type, Seen);
}

// Whether `Argument` is the type `Built`, or one of its template type arguments, all without qualifiers.
bool argumentsInclude(ArrayRef<TemplateArgument> Args, QualType Argument) {
  return llvm::any_of(Args, [&](const TemplateArgument &A) {
    return A.getKind() == TemplateArgument::Pack ? argumentsInclude(A.pack_elements(), Argument)
                                                 : A.getKind() == TemplateArgument::Type &&
                                                       A.getAsType().getCanonicalType().getUnqualifiedType() == Argument;
  });
}

// A value that the library reads without running code of the file. It is a number, or an enum, which has no constructor.
// Or it is a type of the library whose type arguments all count the same way. Decisions 0045 and 0046.
// A type of the file takes its copy through a constructor of its own. That is code of the file, and it may write its argument.
// So does a library type that holds one, because C++23 gives `pair` and `tuple` a constructor that forwards a non-const reference.
// Any other type fails closed.
bool isLibraryValue(QualType Type);

bool argumentsAreLibraryValues(ArrayRef<TemplateArgument> Args) {
  return llvm::all_of(Args, [](const TemplateArgument &A) {
    switch (A.getKind()) {
    case TemplateArgument::Type:
      return isLibraryValue(A.getAsType());
    case TemplateArgument::Pack:
      return argumentsAreLibraryValues(A.pack_elements());
    case TemplateArgument::Integral:
      return true;
    default:
      return false;
    }
  });
}

bool isLibraryValue(QualType Type) {
  Type = Type.getCanonicalType().getUnqualifiedType();
  if (Type->isArithmeticType() || Type->isEnumeralType())
    return true;
  const CXXRecordDecl *Record = Type->getAsCXXRecordDecl();
  if (!Record || !inLibrary(Record))
    return false;
  // A member class, a template or not, holds what the type around it holds, decision 0046.
  // `map<K, V, C>::value_compare` holds the comparator `C`, and `elements_view<V, N>::_Iterator<false>` holds the view `V`.
  const auto *Spec = dyn_cast<ClassTemplateSpecializationDecl>(Record);
  const auto *Outer = dyn_cast<CXXRecordDecl>(Record->getDeclContext());
  return (!Spec || argumentsAreLibraryValues(Spec->getTemplateArgs().asArray())) &&
         (!Outer || isLibraryValue(Record->getASTContext().getRecordType(Outer)));
}

bool isBuiltOrArgument(QualType Argument, QualType Built) {
  Argument = Argument.getCanonicalType().getUnqualifiedType();
  const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(Built->getAsCXXRecordDecl());
  return Argument == Built.getCanonicalType().getUnqualifiedType() || (Spec && argumentsInclude(Spec->getTemplateArgs().asArray(), Argument));
}

// A value gives a way to write when it is a non-const lvalue. It does so too when its type carries one, as a const lvalue does.
// A copy of a class that carries no way to write is a read of its value, decision 0041.
bool grantsWrite(const Expr *E) { return (E->isGLValue() && !E->getType().isConstQualified()) || givesWrite(E->getType()); }

// The element access of a sequence of the library on its object: `operator[]`, `at`, `front` and `back`. It gives an element and writes
// nothing, also the non-const one. A span gives a reference to its element from a const call. `std::map` is no sequence: its subscript
// inserts. The place decides, not the namespace, as for the rest of the library.
bool isElementAccess(const FunctionDecl *Function) {
  const auto *Method = dyn_cast_or_null<CXXMethodDecl>(Function);
  const CXXRecordDecl *Owner = Method ? Method->getParent() : nullptr;
  return Owner && Owner->getDeclName().isIdentifier() && inLibrary(Owner) &&
         llvm::is_contained({"array", "vector", "deque", "basic_string", "span"}, Owner->getName()) &&
         (Method->getOverloadedOperator() == OO_Subscript ||
          (Method->getDeclName().isIdentifier() && llvm::is_contained({"at", "front", "back"}, Method->getName())));
}

// An expression that reaches through a const handle. One kind is an access of an owner, as `isOwnerAccess` says.
// Its owner is const as declared, or is itself reached through a const handle.
// The other kind is the name of a reference loop variable of a range-for whose range does. It names an element of the range.
bool reachesThroughConstHandle(const Expr *E) {
  if (const auto *Ref = dyn_cast<DeclRefExpr>(E)) {
    const auto *Var = dyn_cast<VarDecl>(Ref->getDecl());
    return Var && Var->isCXXForRangeDecl() && Var->getType()->isReferenceType() && rootsOf(Ref).ConstHandle;
  }
  const auto *Call = dyn_cast<CallExpr>(E);
  return Call && isOwnerAccess(Call) && rootsOf(Call).ConstHandle;
}

// Whether a value that reaches through a const handle ends in a use that is no read, decision 0040.
// The value goes up through the nodes that pass it on. They are a bracket, an implicit cast, a member, an element, an address,
// a dereference, an operand, an arm of a conditional, and `std::as_const`.
// It stops where it gives no way to write: a const lvalue that carries none, a number, a pointer to const, a span of const.
// These are reads: a const method on it, a view of const elements, a statement that drops it, and an operand that no code runs.
// A const method on it is a read when its result gives no way to write. A result that gives one is followed from the call.
// Any other use is refused. That is a store, an argument, a return, a capture, a brace list, an explicit cast, and a use that no case knows.
// ponytail: any implicit variable with an initializer is the range of a range-for, which the check of the `for` judges.
// Upgrade: ask whether the variable is the range of a range-for.
bool leaks(ASTContext &Context, const Expr *Node) {
  if (!grantsWrite(Node))
    return false;
  const DynTypedNodeList Parents = Context.getParents(*Node);
  if (Parents.empty())
    return true;
  for (const DynTypedNode &Parent : Parents) {
    const auto *S = Parent.get<Stmt>();
    if (!S) {
      const auto *Var = Parent.get<VarDecl>();
      if ((Parent.get<Decl>() || Parent.get<CXXCtorInitializer>()) && !(Var && Var->isImplicit()))
        return true;
      continue;
    }
    // A method called on the object. A static method reads nothing of it. A non-const method is a use that is no read. A const method and
    // an element access are reads when the result carries no way to write. Else the walk goes on from the call, decision 0041.
    const auto MethodLeaks = [&](const CXXMethodDecl *Method, const CallExpr *Call) {
      return !Method->isStatic() && ((!Method->isConst() && !isElementAccess(Method)) || leaks(Context, Call));
    };
    bool Leak = true;
    if (const auto *Member = dyn_cast<MemberExpr>(S)) {
      if (const auto *Method = dyn_cast<CXXMethodDecl>(Member->getMemberDecl()))
        // The member is the callee. The call is the parent of the member.
        Leak = llvm::any_of(Context.getParents(*Member), [&](const DynTypedNode &Up) {
          return Up.get<CallExpr>() ? MethodLeaks(Method, Up.get<CallExpr>()) : !Method->isStatic();
        });
      else
        Leak = !isa<VarDecl>(Member->getMemberDecl()) && leaks(Context, Member);
    } else if (const auto *Cast = dyn_cast<ExplicitCastExpr>(S)) {
      // A cast of a pointer to an integer is no read. The walk refuses it here, so it need not follow the integer.
      Leak = Cast->getCastKind() == CK_PointerToIntegral || grantsWrite(Cast);
    } else if (const auto *Call = dyn_cast<CallExpr>(S)) {
      // A member operator is a method called on its first operand, as `*h` and `h[i]` are.
      const auto *Method = dyn_cast_or_null<CXXMethodDecl>(Call->getDirectCallee());
      if (Method && !Method->isStatic() && isa<CXXOperatorCallExpr>(Call) && Call->getArg(0) == Node)
        Leak = MethodLeaks(Method, Call);
      else
        Leak = !isAsConst(Call->getDirectCallee()) || leaks(Context, Call);
    } else if (const auto *Construct = dyn_cast<CXXConstructExpr>(S)) {
      // A constructor of the library that builds a value of the library which carries no way to write, from an lvalue, is a copy.
      // It reads the lvalue, whatever reference the constructor takes. C++23 adds `pair(pair<U1, U2>&)`, and `optional(U&&)` takes
      // a forwarding reference. An xvalue is no read, because a move takes from the object. A function of the library is no constructor:
      // what its result carries says nothing of what it did to its arguments.
      // The argument is of the type that is built, or of one of its type arguments, decision 0044.
      // Another constructor may call a method of the file on what it is given.
      // `std::mt19937` calls `generate` on a seed sequence, and `std::thread` runs a callable.
      // The argument is also a value of the library, decisions 0045 and 0046. `std::optional<W>` forwards a non-const `W&` to the
      // constructors of `W`, and a `W(W&)` of the file may write its argument.
      const CXXRecordDecl *Built = Construct->getType()->getAsCXXRecordDecl();
      const bool Copy = Node->isLValue() && Built && inLibrary(Built) && inLibrary(Construct->getConstructor()) &&
                        isLibraryValue(Node->getType()) && isBuiltOrArgument(Node->getType(), Construct->getType()) &&
                        !givesWrite(Construct->getType());
      Leak = !Copy && (!asSpan(Construct->getType()) || isMutableType(Construct->getType()));
    } else if (const auto *Binary = dyn_cast<BinaryOperator>(S)) {
      // A pointer to member reaches a member that no name shows.
      Leak = Binary->isAssignmentOp() || Binary->getOpcode() == BO_PtrMemD || Binary->getOpcode() == BO_PtrMemI ||
             (!(Binary->isCommaOp() && Binary->getLHS() == Node) && leaks(Context, Binary));
    } else if (const auto *Unary = dyn_cast<UnaryOperator>(S)) {
      Leak = Unary->isIncrementDecrementOp() || Unary->getOpcode() == UO_Coawait || leaks(Context, Unary);
    } else if (const auto *Conditional = dyn_cast<AbstractConditionalOperator>(S)) {
      Leak = Conditional->getCond() != Node && leaks(Context, Conditional);
    } else if (isa<ParenExpr, FullExpr, MaterializeTemporaryExpr, CXXBindTemporaryExpr, ImplicitCastExpr, ArraySubscriptExpr>(S)) {
      Leak = leaks(Context, cast<Expr>(S));
    } else if (const auto *List = dyn_cast<InitListExpr>(S)) {
      // A brace list has two forms. The syntactic one holds the expressions as written, and the semantic one holds them with their
      // conversions, a copy among them. The parent map names the semantic list as the parent of both. The use is the one where the
      // node is an element of the list, which is the semantic form with the conversions applied.
      Leak = llvm::is_contained(List->inits(), Node);
    } else if (const auto *Block = dyn_cast<CompoundStmt>(S)) {
      // The last statement of a statement expression is its value.
      Leak = Block->body_back() == Node && llvm::any_of(Context.getParents(*Block), [](const DynTypedNode &Up) { return Up.get<StmtExpr>(); });
    } else if (isa<IfStmt, WhileStmt, DoStmt, ForStmt, SwitchStmt, CaseStmt, DefaultStmt, LabelStmt, AttributedStmt, UnaryExprOrTypeTraitExpr,
                   CXXNoexceptExpr, CXXTypeidExpr>(S)) {
      Leak = false;
    }
    if (Leak)
      return true;
  }
  return false;
}

// cplusp-const-handle: decisions 0033, 0038 and 0040. A const handle gives reads only.
// The check finds each expression that reaches through a const unique_ptr or shared_ptr.
// It follows the expression up to the first node that is no step of a path. That node is refused unless it is a read.
// `leaks` lists the steps and the reads. The check does not list the ways a write leaves a handle.
// A range-for whose range reaches through a const handle is refused in two cases.
// Its loop variable is a non-const reference, or a value that carries a way to write. Or the compiler's call of `begin` or `end` may change state.
// That is a call outside std, and it is a non-const call on what the handle owns.
class ConstHandleCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(expr(anyOf(callExpr(), declRefExpr()), judged()).bind("source"), this);
    Finder->addMatcher(cxxForRangeStmt(judged()).bind("for"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    if (const auto *Loop = Result.Nodes.getNodeAs<CXXForRangeStmt>("for")) {
      const VarDecl *Variable = Loop->getLoopVariable();
      // A loop variable that is a mutable reference, or a value that carries a way to write, as the proxy of a `vector<bool>` does.
      if (((Variable && (isMutableType(Variable->getType()) || givesWrite(Variable->getType()))) || callsMutableBeginOrEnd(Loop, *Result.SourceManager)) &&
          rootsOf(Loop->getRangeInit()).ConstHandle)
        diag(Loop->getBeginLoc(), "a write through a const handle");
      return;
    }
    const auto *Source = Result.Nodes.getNodeAs<Expr>("source");
    if (reachesThroughConstHandle(Source) && leaks(*Result.Context, Source))
      diag(Source->getBeginLoc(), "a write through a const handle");
  }

private:
  // The compiler's calls of `begin` and `end` on the range are the initializers of `__begin` and `__end`. A callee of the library is a
  // container that the library wrote, and a non-const `begin` of it changes nothing. The location decides, not the namespace: a file may
  // open `namespace std` and declare a `begin` that writes. Any other callee that may change state is refused.
  static bool callsMutableBeginOrEnd(const CXXForRangeStmt *Loop, const SourceManager &SM) {
    for (const Stmt *Part : {Loop->getBeginStmt(), Loop->getEndStmt()}) {
      const auto *Declaration = dyn_cast_or_null<DeclStmt>(Part);
      const auto *Var = Declaration ? dyn_cast_or_null<VarDecl>(Declaration->getSingleDecl()) : nullptr;
      const auto *Call = Var && Var->getInit() ? dyn_cast<CallExpr>(Var->getInit()->IgnoreImplicit()->IgnoreParens()) : nullptr;
      const FunctionDecl *Function = Call ? Call->getDirectCallee() : nullptr;
      if (Function && !SM.isInSystemHeader(Function->getLocation()) && mayChangeState(Function))
        return true;
    }
    return false;
  }
};

// Names in std that return an iterator, a reference, a cast or a new value, and change nothing through their parameters.
// The object or the argument may be non-const. A forwarding reference instantiates as a non-const reference, which is why `make_pair`
// and `get` are here. So `std::sort(v.begin(), v.end())` and `v.front() + v.back()` are no pair of changes by their parameters.
// What their code runs still counts, decision 0038. A copy that `make_pair` makes runs the copy constructor.
// A function of the same name outside std is a change.
bool changesNothing(const FunctionDecl *Function) {
  return inStdNamespace(Function) && Function->getDeclName().isIdentifier() &&
         llvm::is_contained({"begin", "end", "cbegin", "cend", "rbegin", "rend", "crbegin", "crend", "at", "front", "back", "move", "forward",
                             "as_const", "make_pair", "make_tuple", "get", "tie"},
                            Function->getName());
}

// Calls Visit on a node and on everything that runs where the node is written, decision 0038. That is its children, the expression of a
// default argument, the expression of a default member initializer, and the capture initializers of a lambda. It is not the body of
// the lambda, which runs where the lambda is called. An unevaluated operand does not run: `sizeof`, `alignof`, `noexcept` and `typeid`.
// A default argument and a default member initializer have no children of their own, and the code that runs is their expression.
template <typename F> void visitRuns(const Stmt *S, const F &Visit) {
  if (!S || isa<UnaryExprOrTypeTraitExpr, CXXNoexceptExpr, CXXTypeidExpr>(S))
    return;
  Visit(S);
  if (const auto *Default = dyn_cast<CXXDefaultArgExpr>(S))
    visitRuns(Default->getExpr(), Visit);
  else if (const auto *Init = dyn_cast<CXXDefaultInitExpr>(S))
    visitRuns(Init->getExpr(), Visit);
  else if (const auto *Lambda = dyn_cast<LambdaExpr>(S))
    for (const Expr *Capture : Lambda->capture_inits())
      visitRuns(Capture, Visit);
  else
    for (const Stmt *Child : S->children())
      visitRuns(Child, Visit);
}

// The table of the lowered form, decision 0037, which the state check reads too. Defined with it.
// A call of `Callee` changes a global when its lines list one or its code in the table writes one or holds a refusal.
// It also changes a global when it has no body and no lines.
bool tableChanges(const FunctionDecl *Callee);
void startTable();
void giveTable(ASTContext *Context);
// The matchers that feed the table, which whichever check is on registers, and the one place that reads their matches.
void registerTableMatchers(MatchFinder *Finder, MatchFinder::MatchCallback *Callback);
bool collectForTable(const MatchFinder::MatchResult &Result);

// A node that changes state: an assignment, an increment, a call of a function that may change state, or a construction
// with a parameter the constructor can write through. A std::span is a view, and cutting one changes nothing, so
// `fill(v, v)` is a matter for the row aliasing. The first part of the rule for a call, a mutable parameter or a non-const method, is
// the callee's own kind. For an operator other than `()` it is an assignment or an increment. The table adds the rest: what the callee
// lists, what its code does, and what an override of it does. The std functions of `changesNothing` are no change by their parameters.
// Their code still counts, through the table.
bool isChange(const Stmt *S) {
  if (const auto *Unary = dyn_cast<UnaryOperator>(S))
    return Unary->isIncrementDecrementOp();
  if (const auto *Binary = dyn_cast<BinaryOperator>(S))
    return Binary->isAssignmentOp();
  if (const auto *Construct = dyn_cast<CXXConstructExpr>(S)) {
    // A constructor of a system header builds a std object. The compiler builds some of them for a rewritten comparison.
    // The `__unspec` of `o < 5` on an optional is one, and no author wrote it. Its parameters are the library's business.
    // What its code does counts, at any depth, and a line does not stop it.
    // A copy of a container runs the copy constructors of its elements. One of them may write a global with no line to say so.
    const CXXConstructorDecl *Constructor = Construct->getConstructor();
    const bool Library = Constructor->getASTContext().getSourceManager().isInSystemHeader(Constructor->getLocation());
    return !asSpan(Construct->getType()) && ((!Library && hasMutableParameter(Constructor)) || tableChanges(Constructor));
  }
  if (const auto *Call = dyn_cast<CallExpr>(S)) {
    const FunctionDecl *Callee = Call->getDirectCallee();
    if (!Callee)
      return false;
    // An operator other than () is a change by its own kind, an assignment or an increment, so `v[i]` on a non-const vector is none.
    // Whatever the operator, what the callee lists and what its code does count too.
    const auto *Operator = dyn_cast<CXXOperatorCallExpr>(S);
    const bool ByKind = Operator && Operator->getOperator() != OO_Call ? isAssignmentOrIncrement(Operator->getOperator()) : mayChangeState(Callee);
    return (!changesNothing(Callee) && ByKind) || tableChanges(Callee);
  }
  return false;
}

// ponytail: two ceilings. A reference member lets a const method change state, and the check calls that method pure.
// A call through a function pointer or a member pointer has no callee the check can read.
// Upgrade: read the type of a pointer.
bool changes(const Stmt *S) {
  bool Found = false;
  visitRuns(S, [&](const Stmt *Node) { Found = Found || isChange(Node); });
  return Found;
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

// What one node adds to the effects. The nodes under it are the visitor's business.
void nodeEffects(const Stmt *S, Effects &E) {
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
}

// The effects of everything that runs where the node is written, the same nodes as `changes` visits.
void effects(const Stmt *S, Effects &E) {
  visitRuns(S, [&](const Stmt *Node) { nodeEffects(Node, E); });
}

// cplusp-evaluation-order: a node with two unordered children that each change state, decision 0026. When exactly one changes
// state, no other unordered child reads what the change can reach, decision 0033.
// The table of the lowered form exists at the end of the translation unit, so the check collects the nodes and judges them then.
class EvaluationOrderCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void onStartOfTranslationUnit() override {
    startTable();
    Nodes.clear();
  }
  void registerMatchers(MatchFinder *Finder) override {
    registerTableMatchers(Finder, this);
    Finder->addMatcher(expr(judged()).bind("expr"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    giveTable(Result.Context);
    if (!collectForTable(Result))
      Nodes.push_back(Result.Nodes.getNodeAs<Expr>("expr"));
  }
  void onEndOfTranslationUnit() override {
    for (const Expr *Node : Nodes)
      judge(Node);
  }

private:
  std::vector<const Expr *> Nodes;

  void judge(const Expr *Node) {
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
    // Parse in quad precision first, then convert to the type of the literal. Parsing straight into a double does not report an integer above 2^63 that a
    // double cannot hold, such as 9223372036854775809.0, decision 0027. Either step may lose information.
    llvm::APFloat Value(llvm::APFloat::IEEEquad());
    auto Status = Value.convertFromString(Text, llvm::APFloat::rmNearestTiesToEven);
    if (!Status) {
      llvm::consumeError(Status.takeError());
      return;
    }
    bool LosesInfo = false;
    const llvm::APFloat::opStatus Converted = Value.convert(Result.Context->getFloatTypeSemantics(Literal->getType()), llvm::APFloat::rmNearestTiesToEven, &LosesInfo);
    if ((*Status & llvm::APFloat::opInexact) || (Converted & llvm::APFloat::opInexact) || LosesInfo)
      diag(Result.SourceManager->getFileLoc(Loc), "floating-point literal is not exactly a double");
  }
};

// ---------------------------------------------------------------- cplusp-raw-copy, decisions 0116 to 0120: the row type_punning
// A raw copy of bytes can make a value that its type does not have. The check judges a bit cast, memcpy, memmove, memset and a cast to non-const bytes.

// The std::byte of the system header. It holds no bad value, and it is a view as bytes. A std::byte that the file declares is an enum like any other.
bool isSystemByte(QualType T, const SourceManager &SM) {
  const auto *Enum = dyn_cast<EnumType>(T.getCanonicalType().getTypePtr());
  const EnumDecl *Decl = Enum ? Enum->getDecl() : nullptr;
  return Decl && Decl->getName() == "byte" && Decl->getDeclContext()->isStdNamespace() && SM.isInSystemHeader(Decl->getLocation());
}

// char, unsigned char or the std::byte of the system header, with any cv: the types that C++ lets any object be read as.
bool isByteScalar(QualType T, const SourceManager &SM) {
  T = T.getCanonicalType();
  if (isSystemByte(T, SM))
    return true;
  const auto *Builtin = dyn_cast<BuiltinType>(T.getTypePtr());
  return Builtin && (Builtin->getKind() == BuiltinType::Char_S || Builtin->getKind() == BuiltinType::Char_U || Builtin->getKind() == BuiltinType::UChar);
}

// Bytes: a byte scalar, an array of bytes, or a class that holds only bytes, such as std::array<uint8_t, 8>.
bool isBytes(QualType T, const SourceManager &SM) {
  T = T.getCanonicalType();
  if (isByteScalar(T, SM))
    return true;
  if (const auto *Array = T->getAsArrayTypeUnsafe())
    return isBytes(Array->getElementType(), SM);
  const CXXRecordDecl *RD = T->getAsCXXRecordDecl();
  if (!RD || !RD->hasDefinition() || RD->isUnion())
    return false;
  RD = RD->getDefinition();
  for (const CXXBaseSpecifier &Base : RD->bases())
    if (!isBytes(Base.getType(), SM))
      return false;
  bool Any = RD->getNumBases() != 0;
  for (const FieldDecl *Field : RD->fields()) {
    if (Field->isBitField() || !isBytes(Field->getType(), SM))
      return false;
    Any = true;
  }
  return Any;
}

// Whether a type holds a bad value at some depth, decisions 0118 and 0119: a pointer, a pointer to a member, a reference, an enum other than the system
// std::byte, or a bool. The depth covers a field, a base and an element of an array. Any bit pattern of an integer or a floating type is a value.
bool holdsBadValue(QualType T, const SourceManager &SM, llvm::SmallPtrSetImpl<const CXXRecordDecl *> &Seen) {
  T = T.getCanonicalType();
  if (isSystemByte(T, SM))
    return false;
  if (T->isPointerType() || T->isMemberPointerType() || T->isReferenceType() || T->isEnumeralType() || T->isBooleanType())
    return true;
  if (const auto *Array = T->getAsArrayTypeUnsafe())
    return holdsBadValue(Array->getElementType(), SM, Seen);
  const CXXRecordDecl *RD = T->getAsCXXRecordDecl();
  if (!RD || !RD->hasDefinition() || !Seen.insert(RD->getDefinition()).second)
    return false;
  RD = RD->getDefinition();
  // A class with a virtual function or a virtual base holds a hidden pointer, decision 0120.
  if (RD->isDynamicClass())
    return true;
  for (const CXXBaseSpecifier &Base : RD->bases())
    if (holdsBadValue(Base.getType(), SM, Seen))
      return true;
  for (const FieldDecl *Field : RD->fields())
    if (holdsBadValue(Field->getType(), SM, Seen))
      return true;
  return false;
}

bool holdsBadValue(QualType T, const SourceManager &SM) {
  llvm::SmallPtrSet<const CXXRecordDecl *, 8> Seen;
  return holdsBadValue(T, SM, Seen);
}

// Whether a type has padding at some depth, decision 0119: a gap between its sub-objects in the layout of the compiler, at any depth. A union has
// padding when a member is smaller than the union. A floating type that does not fill its size, such as long double, has padding.
bool hasPadding(QualType T, ASTContext &Context, llvm::SmallPtrSetImpl<const CXXRecordDecl *> &Seen) {
  T = T.getCanonicalType();
  if (const auto *Array = T->getAsArrayTypeUnsafe())
    return hasPadding(Array->getElementType(), Context, Seen);
  if (T->isFloatingType())
    return llvm::APFloat::getSizeInBits(Context.getFloatTypeSemantics(T)) < Context.getTypeSize(T);
  const CXXRecordDecl *RD = T->getAsCXXRecordDecl();
  if (!RD || !RD->hasDefinition() || !Seen.insert(RD->getDefinition()).second)
    return false;
  RD = RD->getDefinition();
  const ASTRecordLayout &Layout = Context.getASTRecordLayout(RD);
  const uint64_t Size = Context.toBits(Layout.getSize());
  // The sub-objects as ranges of bits.
  std::vector<std::pair<uint64_t, uint64_t>> Ranges;
  for (const CXXBaseSpecifier &Base : RD->bases()) {
    const CXXRecordDecl *BaseDecl = Base.getType()->getAsCXXRecordDecl();
    if (Base.isVirtual() || !BaseDecl)
      return true;
    // An empty base takes no bits, decision 0120.
    if (BaseDecl->isEmpty())
      continue;
    if (hasPadding(Base.getType(), Context, Seen))
      return true;
    const uint64_t At = Context.toBits(Layout.getBaseClassOffset(BaseDecl));
    Ranges.push_back({At, At + Context.getTypeSize(Base.getType())});
  }
  if (RD->isUnion()) {
    for (const FieldDecl *Field : RD->fields())
      if (hasPadding(Field->getType(), Context, Seen) || (Field->isBitField() ? Field->getBitWidthValue(Context) : Context.getTypeSize(Field->getType())) < Size)
        return true;
    return false;
  }
  for (const FieldDecl *Field : RD->fields()) {
    // A field of size zero takes no bits, decision 0120.
    if (Field->isZeroSize(Context))
      continue;
    if (hasPadding(Field->getType(), Context, Seen))
      return true;
    const uint64_t At = Layout.getFieldOffset(Field->getFieldIndex());
    Ranges.push_back({At, At + (Field->isBitField() ? Field->getBitWidthValue(Context) : Context.getTypeSize(Field->getType()))});
  }
  std::sort(Ranges.begin(), Ranges.end());
  uint64_t Covered = 0;
  for (const auto &[From, To] : Ranges) {
    if (From > Covered)
      return true;
    Covered = std::max(Covered, To);
  }
  return Covered < Size;
}

bool hasPadding(QualType T, ASTContext &Context) {
  llvm::SmallPtrSet<const CXXRecordDecl *, 8> Seen;
  return hasPadding(T, Context, Seen);
}

// cplusp-raw-copy: the row is type_punning. It reports
//  - a `std::bit_cast`, a call or its address, whose result holds a bad value, or whose source has padding when the result is not bytes;
//  - a function of the C library that copies or clears raw bytes, whose destination holds a bad value, whose source has padding when the destination is
//    not bytes, or whose destination or source has an unknown or incomplete type, such as `void*`; and the name of such a function that is not called;
//  - a cast to a pointer or a reference to non-const bytes from a pointer or an object that holds a bad value, from `void*`, from an integer, or a
//    `const_cast` that takes const from bytes;
//  - `std::as_writable_bytes` of a span whose element holds a bad value.
// A template is judged at each instance. A matcher cannot look through the fields of a type.
// ponytail: the bit casts of the library are a list kept by hand. Upgrade: match builtinBitCastExpr in the system instantiations, and report it at the
// call site in the user's file.
// ponytail: the functions of the C library are a list kept by hand. Upgrade: ask for each function with a void* parameter that the library writes through.
const char *const WritesBad = "type_punning: The copy writes a type that holds a pointer, a reference, an enum or a bool.";
const char *const ReadsPadding = "type_punning: The copy reads padding into a type that is not bytes.";
const char *const WritesUnknown = "type_punning: The copy writes to a place of unknown type.";
const char *const ReadsUnknown = "type_punning: The copy reads a place of unknown type into a type that is not bytes.";

// The functions of the C library that write or clear raw bytes, with their __builtin_ names.
const char *const RawCopyNames[] = {
    "memcpy", "memmove", "memset", "mempcpy", "memccpy", "bcopy", "bzero", "explicit_bzero",
    "__builtin_memcpy", "__builtin_memmove", "__builtin_memset", "__builtin_mempcpy", "__builtin_memccpy", "__builtin_bcopy", "__builtin_bzero",
    "__builtin___memcpy_chk", "__builtin___memmove_chk", "__builtin___memset_chk", "__builtin___mempcpy_chk",
};

class RawCopyCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(declRefExpr(to(functionDecl(hasAnyName("::std::bit_cast", "::std::experimental::__bit_cast", "::std::experimental::__proposed::simd_bit_cast"))),
                                   unless(isExpansionInSystemHeader()))
                           .bind("bit"),
                       this);
    Finder->addMatcher(declRefExpr(to(functionDecl(hasName("::std::as_writable_bytes"))), unless(isExpansionInSystemHeader())).bind("view"), this);
    std::vector<std::string> Names;
    for (const char *Name : RawCopyNames) {
      Names.push_back(Name);
    }
    // The name of a copy function, called or not. A call is judged by its arguments, and the name that is not called fails closed.
    Finder->addMatcher(declRefExpr(to(functionDecl(hasAnyName(std::vector<StringRef>(Names.begin(), Names.end())))), unless(isExpansionInSystemHeader())).bind("name"), this);
    Finder->addMatcher(explicitCastExpr(anyOf(hasCastKind(CK_BitCast), hasCastKind(CK_LValueBitCast), hasCastKind(CK_IntegralToPointer)), unless(isExpansionInSystemHeader())).bind("cast"), this);
    Finder->addMatcher(explicitCastExpr(anyOf(cxxConstCastExpr(), cStyleCastExpr(hasCastKind(CK_NoOp)), cxxFunctionalCastExpr(hasCastKind(CK_NoOp))), unless(isExpansionInSystemHeader())).bind("unconst"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    Context = Result.Context;
    SM = Result.SourceManager;
    if (const auto *Ref = Result.Nodes.getNodeAs<DeclRefExpr>("bit"))
      bitCast(Ref);
    else if (const auto *View = Result.Nodes.getNodeAs<DeclRefExpr>("view"))
      writableBytes(View);
    else if (const auto *Name = Result.Nodes.getNodeAs<DeclRefExpr>("name"))
      named(Name);
    else if (const auto *Cast = Result.Nodes.getNodeAs<ExplicitCastExpr>("cast"))
      toBytes(Cast);
    else if (const auto *Unconst = Result.Nodes.getNodeAs<ExplicitCastExpr>("unconst"))
      unconst(Unconst);
  }

private:
  ASTContext *Context = nullptr;
  const SourceManager *SM = nullptr;

  void report(SourceLocation At, const char *Why) { diag(SM->getFileLoc(At), "%0") << Why; }

  void bitCast(const DeclRefExpr *Ref) {
    const auto *Function = dyn_cast<FunctionDecl>(Ref->getDecl());
    if (!Function || Function->getReturnType()->isDependentType())
      return;
    const QualType Result = Function->getReturnType();
    if (holdsBadValue(Result, *SM)) {
      report(Ref->getBeginLoc(), WritesBad);
      return;
    }
    if (Function->getNumParams() == 0)
      return;
    QualType From = Function->getParamDecl(0)->getType();
    if (From->isReferenceType())
      From = From->getPointeeType();
    if (!From->isDependentType() && hasPadding(From, *Context) && !isBytes(Result, *SM))
      report(Ref->getBeginLoc(), ReadsPadding);
  }

  // `std::as_writable_bytes` of a span whose element holds a bad value writes bytes into it.
  void writableBytes(const DeclRefExpr *Ref) {
    const auto *Function = dyn_cast<FunctionDecl>(Ref->getDecl());
    if (!Function || Function->getNumParams() == 0 || Function->getParamDecl(0)->getType()->isDependentType())
      return;
    const auto *Span = Function->getParamDecl(0)->getType().getCanonicalType()->getAsCXXRecordDecl();
    const auto *Special = dyn_cast_or_null<ClassTemplateSpecializationDecl>(Span);
    if (Special && Special->getTemplateArgs().size() > 0 && Special->getTemplateArgs()[0].getKind() == TemplateArgument::Type &&
        holdsBadValue(Special->getTemplateArgs()[0].getAsType(), *SM))
      report(Ref->getBeginLoc(), WritesBad);
  }

  // Whether the name is the callee of a call: its parent is the decay to a pointer, and the parent of that is the call.
  bool isCallee(const DeclRefExpr *Ref) const {
    for (const auto &Up : Context->getParents(*Ref))
      if (const auto *Decay = Up.get<ImplicitCastExpr>())
        for (const auto &Above : Context->getParents(*Decay))
          if (const auto *Call = Above.get<CallExpr>(); Call && Call->getCallee() == Decay)
            return true;
    return false;
  }

  // The name of a copy function. A call is judged by its arguments. A name that is not called fails closed.
  void named(const DeclRefExpr *Ref) {
    if (!isCallee(Ref)) {
      report(Ref->getBeginLoc(), WritesUnknown);
      return;
    }
    for (const auto &Up : Context->getParents(*Ref))
      for (const auto &Above : Context->getParents(Up))
        if (const auto *Call = Above.get<CallExpr>())
          memory(Call, cast<FunctionDecl>(Ref->getDecl()));
  }

  // The type that a pointer expression points to, before the conversion to void*, or a null type when the expression is no pointer or an array.
  QualType pointee(const Expr *E) const {
    E = E->IgnoreParenImpCasts();
    const QualType T = E->getType().getCanonicalType();
    if (T->isPointerType())
      return T->getPointeeType();
    if (T->isArrayType())
      return T;
    return QualType();
  }

  void memory(const CallExpr *Call, const FunctionDecl *Callee) {
    // The name without its prefix and suffix: __builtin___memcpy_chk is memcpy.
    StringRef Name = Callee->getName();
    Name.consume_front("__builtin___") || Name.consume_front("__builtin_");
    Name.consume_back("_chk");
    const bool Reversed = Name == "bcopy";
    const bool Copies = Name == "memcpy" || Name == "memmove" || Name == "mempcpy" || Name == "memccpy" || Reversed;
    const unsigned ToAt = Reversed ? 1 : 0, FromAt = Reversed ? 0 : 1;
    if (Call->getNumArgs() <= (Copies ? 1u : 0u) || Call->getArg(ToAt)->isTypeDependent() || (Copies && Call->getArg(FromAt)->isTypeDependent()))
      return;
    const QualType To = pointee(Call->getArg(ToAt));
    if (To.isNull() || To->isVoidType() || To->isIncompleteType()) {
      report(Call->getBeginLoc(), WritesUnknown);
      return;
    }
    if (holdsBadValue(To, *SM)) {
      report(Call->getBeginLoc(), WritesBad);
      return;
    }
    if (!Copies || isBytes(To, *SM))
      return;
    const QualType From = pointee(Call->getArg(FromAt));
    if (From.isNull() || From->isVoidType() || From->isIncompleteType())
      report(Call->getBeginLoc(), ReadsUnknown);
    else if (hasPadding(From, *Context))
      report(Call->getBeginLoc(), ReadsPadding);
  }

  // The pointer or reference type that a cast writes, as the object type, or a null type.
  QualType writtenObject(const ExplicitCastExpr *Cast) const {
    const QualType Written = Cast->getTypeAsWritten().getCanonicalType();
    return Written->isPointerType() || Written->isReferenceType() ? Written->getPointeeType() : QualType();
  }

  // The object that a cast reads: the pointee of a pointer, or the object of a reference cast. Null when the source is no pointer.
  QualType readObject(const ExplicitCastExpr *Cast) const {
    const QualType From = Cast->getSubExpr()->getType().getCanonicalType();
    if (Cast->getTypeAsWritten()->isPointerType())
      return From->isPointerType() ? From->getPointeeType() : QualType();
    return From;
  }

  void toBytes(const ExplicitCastExpr *Cast) {
    const QualType To = writtenObject(Cast);
    if (To.isNull() || To.isConstQualified() || !isByteScalar(To, *SM) || Cast->getSubExpr()->isTypeDependent())
      return;
    const QualType From = readObject(Cast);
    if (From.isNull() || From->isVoidType() || From->isIncompleteType())
      report(Cast->getBeginLoc(), WritesUnknown);
    else if (holdsBadValue(From, *SM))
      report(Cast->getBeginLoc(), WritesBad);
  }

  // A const_cast that takes const away from bytes makes a view that can write the object, which the gate cannot see.
  void unconst(const ExplicitCastExpr *Cast) {
    const QualType To = writtenObject(Cast);
    if (To.isNull() || To.isConstQualified() || !isByteScalar(To, *SM) || Cast->getSubExpr()->isTypeDependent())
      return;
    const QualType From = readObject(Cast);
    if (!From.isNull() && From.isConstQualified() && isByteScalar(From, *SM))
      report(Cast->getBeginLoc(), WritesUnknown);
  }
};

bool insidePlain(const Decl *D);  // below, with the markers

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
      // The word `friend` in a plain type is out of view, whatever the friend is. The bot cannot change the type, decision 0053.
      if (isa<FriendDecl>(D) && insidePlain(cast<Decl>(D->getLexicalDeclContext())))
        return;
      for (const Attr *A : D->attrs())
        checkAttribute(A, *Result.SourceManager);
      // A member function with `__restrict` after its parameters promises that `this` does not alias, and no type holds that qualifier.
      if (const auto *Method = dyn_cast<CXXMethodDecl>(D); Method && Method->getMethodQualifiers().hasRestrict())
        diag(Result.SourceManager->getFileLoc(D->getLocation()), "unlisted: The construct is __restrict.");
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
  // The names of the reference parameters of the function that it may write, in all its declarations: a parameter of type `T&` with no const.
  // A name on a modifies or reads line that is one of them is the parameter, not a global, decision 0111. A parameter by value is no
  // name for a modifies line, so a global of the same name stays the global.
  std::vector<std::string> Parameters;
  bool Any = false;  // a `//@` line of any kind is there
  // Every `//@` line in source order: its file, its line number and its text after the `//@`. The translator, cplusp-tree, reads these.
  // A line that a backslash spliced to the next one is here too, with the backslash at the end of its text. It is no `modifies` or `reads`.
  struct Line {
    unsigned File;  // the hash of the FileID
    unsigned Number;
    std::string Text;
    std::vector<std::string> Params;  // the parameter names of the declaration that the line stands on, "" for an unnamed one
    FileID Id;                        // the file of the line, for its name
  };
  std::vector<Line> Lines;
};

// The contract lines of the function that starts at `First`: the contiguous lines above that line that start with `//@`. A
// `CPLUSP_...(...)` marker line does not end the block. Any other line does. The lines come from the source buffer, because `//@`
// is no doc comment and the AST has not got it. A line that holds code before its `//@` is no contract line, so the walk stops at it.
// `Floor` is where the walk ends: it claims no line that starts at or above the line of `Floor`. A loop sets it to the start of the
// body of its function.
// ponytail: a floor in another file than the loop, as under a macro, is ignored. Such a loop can then claim its function's lines, and
// the core refuses them as lines in the wrong place, which is loud. Upgrade: compare the lines in the file of the loop's expansion.
// `SkipComments` steps over a whole-line `//` comment that is no `//@` line, and over a one-line `/* */` comment, decision 0099. Only the lines
// of a body use it.
// ponytail: a block comment over several lines ends the walk. Upgrade: the lexer's comment tokens.
Contract contractAbove(const SourceManager &SM, SourceLocation First, SourceLocation Floor = SourceLocation(), bool SkipComments = false) {
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
  size_t FloorStart = 0;
  if (Floor.isValid()) {
    const auto [FloorFile, FloorOffset] = SM.getDecomposedLoc(SM.getExpansionLoc(Floor));
    if (FloorFile == File) {
      const size_t Newline = Text.substr(0, FloorOffset).rfind('\n');
      FloorStart = Newline == StringRef::npos ? 0 : Newline + 1;
    }
  }
  while (Start > FloorStart) {
    // The line above is the text from the newline before it up to the newline that ends it.
    const size_t End = Start - 1;
    size_t Begin = Text.substr(0, End).rfind('\n');
    Begin = Begin == StringRef::npos ? 0 : Begin + 1;
    StringRef Line = Text.slice(Begin, End).trim();
    Start = Begin;
    if (Begin <= FloorStart && Floor.isValid())
      break;
    if (Line.starts_with("CPLUSP_"))
      continue;
    if (SkipComments && ((Line.starts_with("//") && !Line.starts_with("//@")) || (Line.starts_with("/*") && Line.ends_with("*/"))))
      continue;
    // A comment that ends in a backslash goes on in the next line. So the line above can be the tail of a `//@` line.
    size_t Head = Begin;
    while (Head > 0) {
      const size_t PreviousBegin = Text.substr(0, Head - 1).rfind('\n');
      const size_t From = PreviousBegin == StringRef::npos ? 0 : PreviousBegin + 1;
      if (!Text.slice(From, Head - 1).rtrim().ends_with("\\"))
        break;
      Head = From;
    }
    const bool Spliced = Head != Begin;
    if (Spliced) {
      Line = Text.slice(Head, Text.find('\n', Head)).trim();
      Begin = Start = Head;
    }
    if (!Line.consume_front("//@"))
      break;
    Line = Line.ltrim();
    C.Lines.push_back({File.getHashValue(), SM.getLineNumber(File, Begin), Line.str(), {}, File});
    if (Spliced)
      continue;
    C.Any = true;
    std::vector<std::string> *Names = Line.consume_front("modifies") ? &C.Modifies : Line.consume_front("reads") ? &C.Reads : nullptr;
    if (!Names || (!Line.empty() && !isspace(static_cast<unsigned char>(Line.front()))))
      continue;
    llvm::SmallVector<StringRef, 8> Parts;
    Line.split(Parts, ',', -1, false);
    for (StringRef Name : Parts)
      if (!Name.trim().empty())
        Names->push_back(Name.trim().str());
  }
  std::reverse(C.Lines.begin(), C.Lines.end());  // the walk went upward
  return C;
}

// Where a function starts: its return type, or its name for a constructor. A function template starts at its `template`, and its
// lines sit above that, as in examples/templates.
SourceLocation firstTokenOf(const FunctionDecl *Function) {
  // An abbreviated function template has no `template` keyword, and it begins at its return type, decision 0049.
  if (const FunctionTemplateDecl *Template = Function->getDescribedFunctionTemplate();
      Template && Template->getTemplateParameters()->getTemplateLoc().isValid())
    return Template->getBeginLoc();
  return Function->getOuterLocStart();
}

// ponytail: one ceiling. The lines come from the files of this translation unit, outside the system headers.
// A callee with no lines here brings no lines. So the contract of a callee in a header behind -isystem, or in another file, is not read.
// What its code does still counts, if the translation unit has the body.
// A callee with no body and no lines at all is refused.
// Upgrade: a contract reader that runs on every file, and a record of the lines of every function.
Contract contractOf(const SourceManager &SM, const FunctionDecl *Function) {
  Contract C;
  if (const FunctionDecl *Pattern = Function->getTemplateInstantiationPattern())
    Function = Pattern;
  for (const FunctionDecl *Declaration : Function->redecls()) {
    // The compiler's own functions have no place in the source, and the place of an implicit member is its class.
    if (Declaration->isImplicit() || SM.isInSystemHeader(Declaration->getLocation()))
      continue;
    Contract One = contractAbove(SM, firstTokenOf(Declaration));
    for (Contract::Line &L : One.Lines)
      for (const ParmVarDecl *P : Declaration->parameters())
        L.Params.push_back(P->getNameAsString());
    for (const ParmVarDecl *P : Declaration->parameters())
      if (P->getType()->isLValueReferenceType() && !P->getType()->getPointeeType().isConstQualified())
        C.Parameters.push_back(P->getNameAsString());
    C.Modifies.insert(C.Modifies.end(), One.Modifies.begin(), One.Modifies.end());
    C.Reads.insert(C.Reads.end(), One.Reads.begin(), One.Reads.end());
    C.Any |= One.Any;
    C.Lines.insert(C.Lines.end(), One.Lines.begin(), One.Lines.end());
  }
  return C;
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

// The methods whose lines hold the overrides of `Base`: `Base` itself, or, when nobody wrote `Base`, what it overrides, as far up as that
// goes. The destructor that the compiler wrote for a class has no lines, and its overrides answer to the lines above it. A function
// that is declared `= default` is written, and its lines are its own, empty or not.
std::vector<const CXXMethodDecl *> lineHolders(const CXXMethodDecl *Base) {
  std::vector<const CXXMethodDecl *> Out;
  if (Base->isImplicit())
    for (const CXXMethodDecl *Up : Base->overridden_methods()) {
      const auto More = lineHolders(Up);
      Out.insert(Out.end(), More.begin(), More.end());
    }
  if (Out.empty())
    Out.push_back(Base);
  return Out;
}

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

// The state variables that a list of lines names. A name that no variable has is a parameter or a typo, and the prover has it. A name of a
// parameter of the function is the parameter, even when a variable has the same name, decision 0111.
std::set<std::string> namedState(const std::vector<std::string> &Lines, const std::vector<std::string> &State, const std::vector<std::string> &Parameters = {}) {
  std::set<std::string> Names;
  for (const std::string &Line : Lines)
    if (const std::string *Var = std::find(Parameters.begin(), Parameters.end(), Line) == Parameters.end() ? resolve(Line, State) : nullptr)
      Names.insert(*Var);
  return Names;
}

// The declaration is in the C++ ABI of the compiler's runtime, which the library calls to throw and to catch.
// ponytail: a name test. Another runtime library's namespace is not known. Upgrade: a list of the runtime's namespaces.
bool inAbiNamespace(const Decl *Declaration) {
  for (const DeclContext *Context = Declaration->getDeclContext(); Context; Context = Context->getParent())
    if (const auto *Namespace = dyn_cast<NamespaceDecl>(Context); Namespace && Namespace->getName() == "__cxxabiv1")
      return true;
  return false;
}

// The state a file declares, outside the system headers: in a namespace, a linkage specification, a class or a class template.
void collectState(const DeclContext *Context, const SourceManager &SM, std::vector<std::string> &Out) {
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

// ------------------------------------------------------------ the markers of a function, decisions 0039 and 0047

// The kind a `cplusp:` annotation names, and none when the word is no marker. `cplusp:assume` marks one statement and waits for a case
// that needs it, so on a declaration it is no marker.
enum class MarkerKind { None, Verified, Trusted, Plain };

MarkerKind markerKind(StringRef Annotation) {
  if (Annotation == "cplusp:verified")
    return MarkerKind::Verified;
  if (Annotation == "cplusp:trusted")
    return MarkerKind::Trusted;
  if (Annotation == "cplusp:plain")
    return MarkerKind::Plain;
  return MarkerKind::None;
}

// The declarations of a function in the order the compiler met them. The declarations of a function template are linked the same way.
std::vector<const FunctionDecl *> declarationsOf(const FunctionDecl *Function) {
  std::vector<const FunctionDecl *> Out;
  for (const FunctionDecl *D = Function->getMostRecentDecl(); D; D = D->getPreviousDecl())
    Out.push_back(D);
  std::reverse(Out.begin(), Out.end());
  return Out;
}

// The compiler makes the first declaration of an explicit specialization from its template, with a copy of the attributes. The copy has
// the place of the attribute that it was copied from, so a specialization has a marker only when it wrote one in a place of its own.
bool copiedFromTemplate(const FunctionDecl *Declaration, const Attr *A) {
  if (const FunctionDecl *Pattern = Declaration->getTemplateInstantiationPattern(false))
    for (const FunctionDecl *Of : declarationsOf(Pattern))
      for (const Attr *Original : Of->attrs())
        if (Original->getLocation() == A->getLocation())
          return true;
  return false;
}

// The `cplusp:` annotations that a declaration wrote itself. A later declaration inherits a copy of each, and the copy is skipped.
template <typename F> void forEachMarker(const Decl *Declaration, const F &Visit) {
  const auto *Function = dyn_cast<FunctionDecl>(Declaration);
  for (const Attr *A : Declaration->attrs())
    if (const auto *Note = dyn_cast<AnnotateAttr>(A);
        Note && !A->isInherited() && Note->getAnnotation().starts_with("cplusp:") && !(Function && copiedFromTemplate(Function, A)))
      Visit(Note);
}

// The function an instantiation was made from. Any other function is its own, an explicit specialization too.
const FunctionDecl *patternOf(const FunctionDecl *Function) {
  const FunctionDecl *Pattern = Function->getTemplateInstantiationPattern();
  return Pattern ? Pattern : Function;
}

// The kind of the markers written on the declarations of a function itself, decision 0047. None when no declaration has a marker, and
// none when two name two kinds.
MarkerKind declaredKind(const FunctionDecl *Function) {
  MarkerKind Kind = MarkerKind::None;
  bool Twice = false;
  for (const FunctionDecl *D : declarationsOf(patternOf(Function)))
    forEachMarker(D, [&](const AnnotateAttr *Note) {
      const MarkerKind Named = markerKind(Note->getAnnotation());
      if (Named == MarkerKind::None)
        return;
      if (Kind == MarkerKind::None)
        Kind = Named;
      else if (Kind != Named)
        Twice = true;
    });
  return Twice ? MarkerKind::None : Kind;
}

// Whether a class carries a plain marker on a declaration of its own, decision 0051. An instantiation of a class template has a copy of
// the marker of its pattern. An explicit or a partial specialization is a class of its own and needs a marker of its own, as decision
// 0047 says of the specialization of a function.
bool markedPlain(const CXXRecordDecl *Record) {
  for (const TagDecl *D : Record->redecls())
    for (const Attr *A : D->attrs())
      if (const auto *Note = dyn_cast<AnnotateAttr>(A); Note && markerKind(Note->getAnnotation()) == MarkerKind::Plain)
        return true;
  return false;
}

// The declaration around `D` that holds its name, or the one that holds its text.
const Decl *outerOf(const Decl *D, bool Written) {
  const DeclContext *Outer = Written ? D->getLexicalDeclContext() : D->getDeclContext();
  return Outer ? Decl::castFromDeclContext(Outer) : nullptr;
}

// A friend function whose definition is this declaration.
bool definedFriend(const Decl *D) {
  const auto *F = dyn_cast<FunctionDecl>(D);
  return F && F->getFriendObjectKind() != Decl::FOK_None && F->isThisDeclarationADefinition();
}

// Whether `D` is plain, `D` itself included. Code in a plain function is plain, decision 0048: a lambda, a local class and its members,
// however deep. Clang takes no marker on a lambda, and a plain body is out of the gate's view. A plain class is the same, decision 0051:
// its members, its nested types and the lambdas in it are plain. So is a member defined outside it and a member that the compiler writes.
// The walk goes by where the name lives. A member with a marker of its own, trusted or verified, has that kind, so the class does not
// hold it or the code inside it, as decision 0047 says. A lambda or a local class in a trusted body stays verified.
// A friend is no member, but one that the class defines is code in the body of the class, decision 0053. Its name lives outside the
// class, so the walk goes by where it is written, which keeps the regions and the rule on calls of one mind. A friend that the class only
// declares keeps the kind of its definition.
bool insidePlain(const Decl *D) {
  bool Marked = false;
  for (; D; D = outerOf(D, definedFriend(D)))
    if (const auto *Enclosing = dyn_cast<FunctionDecl>(D)) {
      const MarkerKind Own = declaredKind(Enclosing);
      if (Own == MarkerKind::Plain)
        return true;
      Marked |= Own != MarkerKind::None;
    } else if (const auto *Class = dyn_cast<CXXRecordDecl>(D); Class && !Marked && markedPlain(Class)) {
      return true;
    }
  return false;
}

// Whether the text of `D` is inside the region of something plain that holds it, so that `D` needs no region of its own. A member
// defined outside its class is plain and it is written outside the class.
bool coveredByPlain(const Decl *D) { return insidePlain(D) && insidePlain(outerOf(D, true)); }

// ------------------------------------------------------------ the lowered form, decision 0037

// What a piece of code does to the state: the names it writes and reads, and its refusals. A refusal is a whole message, so the
// function that is judged can report it at the instruction that brought it.
struct Effect {
  std::set<std::string> Writes, Reads, Refusals;
  size_t size() const { return Writes.size() + Reads.size() + Refusals.size(); }
  // Whether this grew.
  bool add(const Effect &Other) {
    const size_t Before = size();
    Writes.insert(Other.Writes.begin(), Other.Writes.end());
    Reads.insert(Other.Reads.begin(), Other.Reads.end());
    Refusals.insert(Other.Refusals.begin(), Other.Refusals.end());
    return size() != Before;
  }
};

// A place in a file, as the debug line table gives it: the file, a line and a column.
// The file is the entry of the file manager. So a header that is included twice is one file, and its lines are the same in both.
struct Place {
  const FileEntry *File = nullptr;
  unsigned Line = 0, Col = 0;
  bool before(const Place &O) const { return Line != O.Line ? Line < O.Line : Col < O.Col; }
};

// A virtual call of the tree: where it is written, the method that the source names, and the function that holds the expression.
// The owner is the canonical declaration of that instantiation, or none if no function holds it.
// The lowered form has an indirect call there. Two functions of a library may hold a call on the same line of a header.
// So the owner tells them apart. The place is numbers, and no source location.
// The second inclusion of a header is another file in the source manager, and the same file in the line table.
struct VirtualCall {
  Place Begin, End;
  const CXXMethodDecl *Method;
  const FunctionDecl *Owner;
};

struct Finding {
  SourceLocation Loc;
  std::string Message;
};

// The code that clang generates for a translation unit, and what each function in it does to the state. Both the state check and the
// sequencing check ask it. It is built once, at the end of the translation unit, on the first question.
class Lowered {
public:
  // What the matchers give it. The virtual calls of the tree. The functions that the file wrote, which the module must hold whether
  // anything calls them or not. Every instantiation of a template, which clang hands to its code generator as it makes it.
  ASTContext *Ctx = nullptr;
  std::vector<VirtualCall> Virtuals;
  std::vector<const FunctionDecl *> Judged, Instances;
  std::vector<const VarDecl *> VarInstances;

  void addVirtual(SourceRange Where, const CXXMethodDecl *Method, const FunctionDecl *Owner) {
    Virtuals.push_back({placeOfExpansion(Where.getBegin()), placeOfExpansion(Where.getEnd()), Method, Owner ? Owner->getCanonicalDecl() : nullptr});
  }

  // Where a location of the tree is, as the line table would give it.
  Place placeOfExpansion(SourceLocation Loc) const {
    const SourceManager &SM = Ctx->getSourceManager();
    const auto [File, Offset] = SM.getDecomposedExpansionLoc(Loc);
    return {SM.getFileEntryForID(File), SM.getLineNumber(File, Offset), SM.getColumnNumber(File, Offset)};
  }

  // The first check to match gives the context.
  void use(ASTContext *Context) {
    if (!Ctx)
      Ctx = Context;
  }

  // The qualified names of the state of this file, found once per translation unit.
  const std::vector<std::string> &state() {
    if (!Collected) {
      collectState(Ctx->getTranslationUnitDecl(), Ctx->getSourceManager(), State);
      llvm::sort(State);
      State.erase(std::unique(State.begin(), State.end()), State.end());
      Collected = true;
    }
    return State;
  }

  // The findings of the state check: one per message per line, found by judging every function that the file wrote.
  const std::vector<Finding> &findings() {
    build();
    return Findings;
  }

  // A call that runs a plain function, decision 0047: where the call is, and the qualified name of the plain function.
  struct PlainCall {
    SourceLocation Loc;
    std::string Name;
  };
  // The calls of the code that the file wrote, from every function of it whatever its kind, that run a plain function. A call runs it
  // when it names it, when the library or a member that the compiler wrote reaches it, when a virtual call can reach it, or when it
  // passes it on as a function constant. The gate asks the kind of the place.
  const std::vector<PlainCall> &plainCalls() {
    build();
    return PlainCalls;
  }

  // The calls of the code that the file wrote that can run an indirect call with no target that the gate can name, decision 0048.
  const std::vector<SourceLocation> &indirectCalls() {
    build();
    return IndirectCalls;
  }

  // False when the compiler could not generate code for the file. Then no call is read.
  bool generated() {
    build();
    return !Failed;
  }

  // Whether a call of `Callee` changes state, as far as its lines and the lowered form say. The first part of the sequencing check's
  // rule, a mutable parameter or a non-const method, is the caller's.
  bool changes(const FunctionDecl *Callee) {
    build();
    if (!contractOf(Ctx->getSourceManager(), Callee).Modifies.empty())
      return true;
    // A file that clang cannot generate code for is refused by the state check. A call that the table cannot read is a change, as a
    // refusal is.
    if (Failed)
      return true;
    const auto Found = ByDecl.find(Callee->getCanonicalDecl());
    if (Found == ByDecl.end()) {
      if (!hasBody(Callee) && opaque(Callee))
        return true;
    } else if (Fns.find(Found->second)->second.Is == Role::Edge ? !edge(Callee).Refusals.empty() : Fns.find(Found->second)->second.Deep) {
      return true;
    }
    // A call through a base may run any override of it in the module.
    if (const auto *Method = dyn_cast<CXXMethodDecl>(Callee))
      for (const llvm::Function *F : Overriders.lookup(cast<CXXMethodDecl>(Method->getCanonicalDecl())))
        if (Fns.find(F)->second.Deep || !contractOf(Ctx->getSourceManager(), Fns.find(F)->second.FD).Modifies.empty())
          return true;
    return false;
  }

private:
  enum class Role { Judged, Carrier, Edge };
  // What a function calls, in the module. The carriers are for the fixpoint of the effects.
  // Every function that has a body is for the bit that the sequencing check reads.
  struct Calls {
    std::vector<const llvm::Function *> Carriers, Bodies;
  };
  // A function of the module, with the declaration of the tree that it came from.
  // A carrier has no lines of its own, so it brings its effect `E` to whoever calls it.
  // A function that the file wrote has its effect too. A call of it brings its lines, and the state check reads one level of tags.
  // That is decision 0037. The sequencing check asks `Deep`. It is set when the code of the function stores a global of the state or
  // holds a refusal. It is also set when the code of anything with a body that it calls does, at any depth. No line stops it.
  // It is also set when the lines of a callee list a name on `modifies`, because `bring` puts those names in `Writes`.
  struct Fn {
    const FunctionDecl *FD = nullptr;
    Role Is = Role::Carrier;
    Effect E;
    Calls C;
    bool Deep = false;
  };
  // Where a pointer comes from. A refusal holds its message, or none for a pointer the gate cannot follow.
  struct Root {
    enum Kind { Global, Local, Func, Refuse } K;
    const llvm::Value *V;
    std::string Why;
  };
  // The objects that a walk has been to, and whether it came through a load of a pointer.
  using Seen = llvm::SmallSet<std::pair<const llvm::Value *, bool>, 16>;

  // The generated module has to outlive nothing of the tree, so the maps below hold what the tree knows about it.
  llvm::LLVMContext LLVM;
  CodeGenOptions CGO;
  HeaderSearchOptions HSO;
  PreprocessorOptions PPO;
  std::unique_ptr<DiagnosticsEngine> Diags;
  std::unique_ptr<CodeGenerator> Gen;
  std::unique_ptr<llvm::Module> Mod;
  llvm::DenseMap<const llvm::Function *, Fn> Fns;
  llvm::DenseMap<const FunctionDecl *, const llvm::Function *> ByDecl;
  llvm::DenseMap<const llvm::GlobalVariable *, std::string> StateOf;
  llvm::DenseMap<const llvm::GlobalVariable *, const VarDecl *> VarOf;
  llvm::DenseSet<const llvm::GlobalVariable *> Known, Library;
  // The loads that find the function of a virtual call, which the match of the call judges.
  llvm::DenseSet<const llvm::Instruction *> Dispatch;
  llvm::DenseMap<const llvm::CallBase *, std::vector<const VirtualCall *>> Matched;
  llvm::DenseMap<const CXXMethodDecl *, std::vector<const llvm::Function *>> Overriders;
  llvm::DenseMap<const llvm::DIFile *, const FileEntry *> Files;
  std::set<std::pair<std::pair<unsigned, unsigned>, std::string>> Reported;
  std::vector<std::string> State;
  std::vector<Finding> Findings;
  std::vector<PlainCall> PlainCalls;
  std::set<std::pair<SourceLocation::UIntTy, std::string>> PlainSeen;
  std::vector<SourceLocation> IndirectCalls;
  std::set<SourceLocation::UIntTy> IndirectSeen;
  bool Collected = false, Built = false, Failed = false;

  // ------------------------------------------------------------ build

  void build() {
    if (Built)
      return;
    Built = true;
    SourceManager &SM = Ctx->getSourceManager();
    const bool Generated = generate();
    // The generator holds the tree, which is gone by the next translation unit.
    Gen.reset();
    if (!Generated) {
      Failed = true;
      Findings.push_back({SM.getLocForStartOfFile(SM.getMainFileID()),
                          "global_state: the compiler could not generate code for this file, so the state check cannot run."});
      return;
    }
    markDispatch();
    // The effect of each function with a body, from its own instructions, then grown by what its carriers bring until nothing changes.
    // Effects only grow and the names are finite, so it ends.
    for (auto &[F, Info] : Fns)
      if (Info.Is != Role::Edge)
        for (const llvm::BasicBlock &BB : *F)
          for (const llvm::Instruction &I : BB)
            instruction(I, Info.E, &Info.C);
    for (bool Changed = true; Changed;) {
      Changed = false;
      for (auto &[F, Info] : Fns)
        for (const llvm::Function *Dep : Info.C.Carriers)
          if (Dep != F)
            Changed |= Info.E.add(Fns.find(Dep)->second.E);
    }
    // The bit for the sequencing check, by the same kind of fixpoint over every call that has a body.
    for (auto &[F, Info] : Fns)
      Info.Deep = !Info.E.Writes.empty() || !Info.E.Refusals.empty();
    for (bool Changed = true; Changed;) {
      Changed = false;
      for (auto &[F, Info] : Fns)
        if (!Info.Deep)
          for (const llvm::Function *Dep : Info.C.Bodies)
            if (Fns.find(Dep)->second.Deep) {
              Info.Deep = Changed = true;
              break;
            }
    }
    for (const auto &[F, Info] : Fns)
      if (Info.Is == Role::Judged)
        judge(*F, Info.FD);
    holdOverrides();
    plainCode();
    indirectCode();
  }

  // Generate the module for the translation unit that the matchers have just read, and read the tree's names off it. False if clang
  // cannot generate code for it.
  bool generate() {
    SourceManager &SM = Ctx->getSourceManager();
    // The tree of a file that does not compile is no input for code generation.
    if (Ctx->getDiagnostics().hasErrorOccurred())
      return false;
    // The diagnostics of code generation are the gate's business, and the gate says one thing about them. A fresh engine counts them.
    Diags = std::make_unique<DiagnosticsEngine>(new DiagnosticIDs, new DiagnosticOptions, new IgnoringDiagConsumer);
    Diags->setSourceManager(&SM);
    // Clang marks a load of a pointer to a vtable `!invariant.group` only when it optimizes, and only when it is told to. It does the
    // marking while it generates code. The module gets no pass but SROA below, so nothing is inlined.
    CGO.OptimizationLevel = 1;
    CGO.StrictVTablePointers = true;
    CGO.setDebugInfo(llvm::codegenoptions::DebugLineTablesOnly);
    CGO.DebugColumnInfo = true;
    Gen.reset(CreateLLVMCodeGen(*Diags, "cplusp", SM.getFileManager().getVirtualFileSystemPtr(), HSO, PPO, CGO, LLVM));
    Gen->Initialize(*Ctx);
    // A copy, because code generation may add declarations to the translation unit.
    const std::vector<Decl *> Top(Ctx->getTranslationUnitDecl()->decls_begin(), Ctx->getTranslationUnitDecl()->decls_end());
    for (Decl *D : Top)
      Gen->HandleTopLevelDecl(DeclGroupRef(D));
    for (const FunctionDecl *FD : Instances)
      Gen->HandleTopLevelDecl(DeclGroupRef(const_cast<FunctionDecl *>(FD)));
    // A table of function pointers is an instantiated variable, and the call through it needs its initializer.
    // Sema hands every instantiated variable definition to the generator this way, a static data member or a variable template.
    for (const VarDecl *Var : VarInstances)
      Gen->HandleCXXStaticMemberVarInstantiation(const_cast<VarDecl *>(Var));
    // An inline function that nothing calls is no part of a build, and the gate judges it all the same. So is a static one.
    for (const FunctionDecl *FD : Judged) {
      const auto *Method = dyn_cast<CXXMethodDecl>(FD);
      if (FD->isDeleted() || FD->isImmediateFunction() || (Method && isLambdaCallOperator(Method)))
        continue;
      if (const auto *Constructor = dyn_cast<CXXConstructorDecl>(FD))
        Gen->GetAddrOfGlobal(GlobalDecl(Constructor, Ctor_Complete), true);
      else if (const auto *Destructor = dyn_cast<CXXDestructorDecl>(FD))
        Gen->GetAddrOfGlobal(GlobalDecl(Destructor, Dtor_Complete), true);
      else
        Gen->GetAddrOfGlobal(GlobalDecl(FD), true);
    }
    Gen->HandleTranslationUnit(*Ctx);
    llvm::Module *M = Gen->GetModule();
    if (!M || Diags->hasErrorOccurred())
      return false;
    // SROA, so that a reference held in a local resolves to what it names.
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
    llvm::FunctionPassManager FPM;
    FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    llvm::ModulePassManager MPM;
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
    for (llvm::Function &F : *M)
      if (!F.isDeclaration())
        F.removeFnAttr(llvm::Attribute::OptimizeNone);
    MPM.run(*M, MAM);
    for (llvm::Function &F : *M) {
      Fn &Info = Fns[&F];
      Info.FD = dyn_cast_or_null<FunctionDecl>(Gen->GetDeclForMangledName(F.getName()));
      Info.Is = F.isDeclaration() ? Role::Edge : Info.FD && isJudged(Info.FD, SM) ? Role::Judged : Role::Carrier;
      if (Info.FD)
        ByDecl.try_emplace(Info.FD->getCanonicalDecl(), &F);
    }
    // A global that the tree does not know, such as a vtable, a string or a guard variable, is no state.
    for (llvm::GlobalVariable &G : M->globals())
      if (const auto *Var = dyn_cast_or_null<VarDecl>(Gen->GetDeclForMangledName(G.getName()))) {
        // A global of a system header is the library's own, as the pointer to a callable that std::call_once keeps in one.
        (SM.isInSystemHeader(Var->getLocation()) ? Library : Known).insert(&G);
        VarOf[&G] = Var;
        if (isState(Var))
          StateOf[&G] = nameOf(Var);
      }
    for (const auto &[F, Info] : Fns)
      if (const auto *Method = dyn_cast_or_null<CXXMethodDecl>(Info.FD))
        overrides(Method, F);
    Mod.reset(Gen->ReleaseModule());
    return true;
  }

  // `F` is the code of `Method`, and so of everything that `Method` overrides, however far up.
  void overrides(const CXXMethodDecl *Method, const llvm::Function *F) {
    for (const CXXMethodDecl *Base : Method->overridden_methods()) {
      auto &List = Overriders[cast<CXXMethodDecl>(Base->getCanonicalDecl())];
      if (!llvm::is_contained(List, F)) {
        List.push_back(F);
        overrides(Base, F);
      }
    }
  }

  // The virtual calls of the tree that an indirect call of the module is. Only the calls that the function holds count.
  // A call that no function holds counts wherever it is. One in a default member initializer is such a call.
  // Every function that makes the object runs it.
  const std::vector<const VirtualCall *> &matched(const llvm::CallBase &CB) {
    const auto Cached = Matched.find(&CB);
    if (Cached != Matched.end())
      return Cached->second;
    auto &Out = Matched[&CB];
    const Place At = placeOf(CB);
    const FunctionDecl *Holder = Fns.find(CB.getFunction())->second.FD;
    if (Holder)
      Holder = Holder->getCanonicalDecl();
    if (At.File)
      for (const VirtualCall &V : Virtuals)
        if (V.Begin.File == At.File && (!V.Owner || V.Owner == Holder) && !At.before(V.Begin) && !V.End.before(At))
          Out.push_back(&V);
    return Out;
  }

  // The virtual dispatches that an indirect call may be. The callee is a slot read from a table.
  // The pointer to the table is a load that clang marked `!invariant.group`.
  // The callee may be a choice between a slot and something else, as a pointer to a member function is.
  // Each dispatch is the load of the slot and the load of the table.
  static llvm::SmallVector<std::pair<const llvm::LoadInst *, const llvm::LoadInst *>, 2> dispatchesOf(const llvm::CallBase &CB) {
    llvm::SmallVector<std::pair<const llvm::LoadInst *, const llvm::LoadInst *>, 2> Out;
    llvm::SmallVector<const llvm::Value *, 4> Objects;
    llvm::getUnderlyingObjects(CB.getCalledOperand(), Objects, nullptr, 0);
    for (const llvm::Value *O : Objects) {
      const auto *Slot = dyn_cast<llvm::LoadInst>(O);
      if (!Slot)
        continue;
      const llvm::Value *P = Slot->getPointerOperand();
      while (const auto *G = dyn_cast<llvm::GEPOperator>(P))
        P = G->getPointerOperand();
      const auto *Table = dyn_cast<llvm::LoadInst>(P);
      if (Table && Table->hasMetadata(llvm::LLVMContext::MD_invariant_group))
        Out.push_back({Slot, Table});
    }
    return Out;
  }

  // The function that a virtual call finds is read from the object: the pointer to the table, then the slot in it.
  // When the tree has the call, the match judges them. So the pointer to the table of a global object needs no following.
  void markDispatch() {
    for (const auto &[F, Info] : Fns) {
      if (Info.Is == Role::Edge)
        continue;
      for (const llvm::BasicBlock &BB : *F)
        for (const llvm::Instruction &I : BB) {
          const auto *CB = dyn_cast<llvm::CallBase>(&I);
          if (!CB || CB->isInlineAsm() || calleeOf(*CB) || matched(*CB).empty())
            continue;
          for (const auto &[Slot, Table] : dispatchesOf(*CB)) {
            Dispatch.insert(Slot);
            Dispatch.insert(Table);
          }
        }
    }
  }

  // One finding for a line and a message.
  void report(SourceLocation Loc, const std::string &Message) {
    const SourceManager &SM = Ctx->getSourceManager();
    if (Reported.insert({{SM.getFileID(Loc).getHashValue(), SM.getExpansionLineNumber(Loc)}, Message}).second)
      Findings.push_back({SM.getExpansionLoc(Loc), Message});
  }

  // An override lists no more than the function it overrides. So a call through the base brings lines that hold for every override.
  // The check of the tree holds a method that has lines. This holds the one that nobody wrote, by what it runs.
  // The destructor of a class with a member that has a destructor of its own is such a method.
  void holdOverrides() {
    const SourceManager &SM = Ctx->getSourceManager();
    for (const auto &[F, Info] : Fns) {
      const auto *Method = dyn_cast_or_null<CXXMethodDecl>(Info.FD);
      if (Info.Is != Role::Carrier || !Method)
        continue;
      const SourceLocation At = Method->getParent()->getLocation();
      for (const CXXMethodDecl *Direct : Method->overridden_methods())
        for (const CXXMethodDecl *Base : lineHolders(Direct)) {
          if (SM.isInSystemHeader(Base->getLocation()))
            continue;
          const Effect Up = linesOf(Base);
          const std::string Of = Method->getNameAsString(), Over = Base->getQualifiedNameAsString();
          for (const std::string &Name : Info.E.Writes)
            if (!Up.Writes.count(Name))
              report(At, "global_state: " + Of + " changes " + Name + ", and the modifies line of " + Over + " does not list it.");
          for (const std::string &Name : Info.E.Reads)
            if (!Up.Writes.count(Name) && !Up.Reads.count(Name))
              report(At, "global_state: " + Of + " reads " + Name + ", and no reads or modifies line of " + Over + " lists it.");
        }
    }
  }

  // A user-written function with a definition in a user file. A lambda's call operator has no lines of its own, so it is a carrier.
  static bool isJudged(const FunctionDecl *FD, const SourceManager &SM) {
    const auto *Method = dyn_cast<CXXMethodDecl>(FD);
    return FD->isThisDeclarationADefinition() && !SM.isInSystemHeader(SM.getExpansionLoc(FD->getBeginLoc())) && !notJudgedFunction(*FD) &&
           !(Method && isLambdaCallOperator(Method));
  }

  // ------------------------------------------------------------ lines and edges

  // What the lines of a function name: the state it lists as changed and as read.
  Effect linesOf(const FunctionDecl *FD) {
    const Contract C = contractOf(Ctx->getSourceManager(), FD);
    Effect E;
    E.Writes = namedState(C.Modifies, state(), C.Parameters);
    E.Reads = namedState(C.Reads, state(), C.Parameters);
    return E;
  }

  // A function that the gate cannot read: no body in the lowered form, and no contract lines. A call of it may change any global. A
  // function that the compiler or a `= default` defines, and a pure virtual function, which an override answers, are no such function.
  bool opaque(const FunctionDecl *FD) {
    return !(FD->isImplicit() || FD->isDefaulted() || FD->isPureVirtual()) && !contractOf(Ctx->getSourceManager(), FD).Any;
  }

  // A function with no body in the module. A system header declares it, or it is a builtin: it brings nothing. Otherwise it brings its
  // lines, and without any the call is refused, whatever namespace the function is in.
  Effect edge(const FunctionDecl *FD) {
    Effect E;
    const SourceManager &SM = Ctx->getSourceManager();
    if (!FD || FD->getBuiltinID() || SM.isInSystemHeader(FD->getLocation()))
      return E;
    E.add(linesOf(FD));
    if (opaque(FD))
      E.Refusals.insert("global_state: " + FD->getNameAsString() + " has no body here and no contract lines, so it may change any global.");
    return E;
  }

  // What a call of `F` brings: the lines of a function the file wrote, the effect of a carrier, what an edge says. A carrier's effect is
  // still growing while the carriers are read, so then the callee is recorded for the fixpoint.
  void bring(const llvm::Function *F, Effect &E, Calls *D) {
    const Fn &Info = Fns.find(F)->second;
    switch (Info.Is) {
    case Role::Judged:
      E.add(linesOf(Info.FD));
      if (D)
        D->Bodies.push_back(F);
      break;
    case Role::Carrier:
      if (D) {
        D->Carriers.push_back(F);
        D->Bodies.push_back(F);
      } else {
        E.add(Info.E);
      }
      break;
    case Role::Edge:
      E.add(edge(Info.FD));
      break;
    }
  }

  // ------------------------------------------------------------ instructions

  static const llvm::Function *calleeOf(const llvm::CallBase &CB) {
    return dyn_cast<llvm::Function>(CB.getCalledOperand()->stripPointerCastsAndAliases());
  }

  // The functions that a constant names, as a table of function pointers does.
  // An intrinsic is no function of the author's, as `llvm.launder.invariant.group` is not.
  // A global is not followed, except a private one with an initializer. The compiler made it for an initializer of its own.
  // A vtable is never private, so the store of its address in a constructor brings nothing.
  static void functionsIn(const llvm::Constant *C, std::vector<const llvm::Function *> &Out, llvm::SmallPtrSetImpl<const llvm::Constant *> &Done) {
    if (const auto *F = dyn_cast<llvm::Function>(C)) {
      if (!F->isIntrinsic())
        Out.push_back(F);
    } else if (const auto *G = dyn_cast<llvm::GlobalVariable>(C); G && G->hasPrivateLinkage() && G->hasInitializer()) {
      if (Done.insert(G).second)
        functionsIn(G->getInitializer(), Out, Done);
    } else if (!isa<llvm::GlobalValue, llvm::BlockAddress>(C) && Done.insert(C).second) {
      for (const llvm::Use &U : C->operands())
        if (const auto *Part = dyn_cast<llvm::Constant>(U.get()))
          functionsIn(Part, Out, Done);
    }
  }

  // A function whose address is an operand of an instruction, other than the callee of a direct call, may be called later.
  // The pointer that holds it may be called by code that has no way to know what the function does.
  // So the instruction brings what a call of it would bring. That covers a store of the address, a select, a phi, an argument and a
  // part of a constant. A constant that the compiler made for an initializer is followed, as the table of an array of function pointers is.
  // `call()` follows the table of the library, where the callee of an indirect call is read from such a global.
  void named(const llvm::Constant *C, Effect &E, Calls *D, llvm::SmallPtrSetImpl<const llvm::Constant *> &Done) {
    std::vector<const llvm::Function *> Functions;
    functionsIn(C, Functions, Done);
    for (const llvm::Function *F : Functions)
      bring(F, E, D);
  }

  void instruction(const llvm::Instruction &I, Effect &E, Calls *D) {
    llvm::SmallPtrSet<const llvm::Constant *, 8> Done;
    for (const llvm::Use &U : I.operands()) {
      const auto *CB = dyn_cast<llvm::CallBase>(&I);
      if (const auto *C = dyn_cast<llvm::Constant>(U.get()); C && !(CB && &U == &CB->getCalledOperandUse() && calleeOf(*CB)))
        named(C, E, D, Done);
    }
    if (const auto *Store = dyn_cast<llvm::StoreInst>(&I))
      access(Store->getPointerOperand(), true, E);
    else if (const auto *Load = dyn_cast<llvm::LoadInst>(&I)) {
      if (!Dispatch.count(Load))
        access(Load->getPointerOperand(), false, E);
    }
    else if (const auto *Rmw = dyn_cast<llvm::AtomicRMWInst>(&I))
      access(Rmw->getPointerOperand(), true, E);
    else if (const auto *Swap = dyn_cast<llvm::AtomicCmpXchgInst>(&I))
      access(Swap->getPointerOperand(), true, E);
    else if (const auto *CB = dyn_cast<llvm::CallBase>(&I))
      call(*CB, E, D);
    else if (const auto *Ret = dyn_cast<llvm::ReturnInst>(&I))
      escape(*Ret, E);
  }

  // A function that returns a reference or a pointer to a global lets its caller reach the global. The type of the return value says
  // how, as the type of a parameter does.
  // ponytail: only a global counts. The aliasing check refuses a reference from a function that the file does not define. Upgrade: refuse a
  // returned pointer whose root is a refusal here too.
  void escape(const llvm::ReturnInst &Ret, Effect &E) {
    if (!Ret.getReturnValue() || !Ret.getReturnValue()->getType()->isPointerTy())
      return;
    const FunctionDecl *FD = Fns.find(Ret.getFunction())->second.FD;
    std::vector<Root> Rs;
    Seen S;
    roots(Ret.getReturnValue(), Rs, S);
    for (const Root &R : Rs)
      if (R.K == Root::Global)
        reach(R, !FD || isMutableType(FD->getReturnType()), E);
  }

  // A store or a load. The roots of the pointer say what it reaches.
  void access(const llvm::Value *Pointer, bool Write, Effect &E) {
    std::vector<Root> Rs;
    Seen S;
    roots(Pointer, Rs, S);
    for (const Root &R : Rs)
      reach(R, Write, E);
  }

  void reach(const Root &R, bool Write, Effect &E) {
    if (R.K == Root::Global) {
      if (const auto Name = StateOf.find(cast<llvm::GlobalVariable>(R.V)); Name != StateOf.end())
        (Write ? E.Writes : E.Reads).insert(Name->second);
    } else if (R.K == Root::Refuse) {
      E.Refusals.insert(!R.Why.empty() ? R.Why
                                       : Write ? "global_state: a write through a pointer the gate cannot follow may reach any global, and no line can list it."
                                               : "global_state: a read through a pointer the gate cannot follow may reach any global, and no line can list it.");
    }
  }

  // The function is the library's own: a system header declares it, or it has no declaration, as the compiler's runtime has none.
  bool inLibrary(const llvm::Function *F) const {
    const FunctionDecl *FD = F ? Fns.find(F)->second.FD : nullptr;
    return !FD || Ctx->getSourceManager().isInSystemHeader(FD->getLocation());
  }

  // What a pointer reaches: the global, local or parameter at its root.
  // The result of a call reaches what the pointers given to the call reach, unless the gate cannot read the function.
  // A pointer that is loaded from memory points where the object that holds it says.
  // The gate follows it to the parameter or local that holds it, as the pointer in a std::vector or a vtable.
  // If a global that the file declares holds it, the pointee is not the global, and nothing can name it.
  // ponytail: a parameter that holds a pointer to a global hides the global. A struct with a raw pointer member is one.
  // The rows raw_pointer, lvalue_references and array_span ban such a pointer in the code that is judged.
  // A span over a global array is included. The row aliasing refuses a global that is passed to a call.
  // Upgrade: follow the stores into the object that holds the pointer.
  // `Via` is the function that does the load, when the pointer was loaded.
  void roots(const llvm::Value *V, std::vector<Root> &Out, Seen &S, bool Loaded = false, const llvm::Function *Via = nullptr) {
    llvm::SmallVector<const llvm::Value *, 4> Objects;
    llvm::getUnderlyingObjects(V, Objects, nullptr, 0);
    for (const llvm::Value *O : Objects) {
      if (!S.insert({O, Loaded}).second)
        continue;
      if (const auto *G = dyn_cast<llvm::GlobalVariable>(O)) {
        // A pointer in a global that the file declares may point at anything. So may one in a global of the library that user code reads.
        // One in a global that the tree does not know, such as a vtable, is the compiler's. The library reads its own.
        const bool Foreign = Known.count(G) || (Library.count(G) && !inLibrary(Via));
        Out.push_back({!Loaded ? Root::Global : Foreign ? Root::Refuse : Root::Local, O, ""});
      } else if (const auto *Load = dyn_cast<llvm::LoadInst>(O)) {
        roots(Load->getPointerOperand(), Out, S, true, Load->getFunction());
      } else if (isa<llvm::AllocaInst, llvm::Argument, llvm::ConstantPointerNull, llvm::UndefValue, llvm::LandingPadInst>(O)) {
        Out.push_back({Root::Local, O, ""});
      } else if (isa<llvm::Function>(O)) {
        Out.push_back({Root::Func, O, ""});
      } else if (const auto *Cast = dyn_cast<llvm::IntToPtrInst>(O)) {
        // A pointer that is made from a number, such as the function in a pointer to a member function, is where the number came from.
        roots(Cast->getOperand(0), Out, S, Loaded, Via);
      } else if (const auto *Extract = dyn_cast<llvm::ExtractValueInst>(O)) {
        roots(Extract->getAggregateOperand(), Out, S, Loaded, Via);
      } else if (const auto *Insert = dyn_cast<llvm::InsertValueInst>(O)) {
        roots(Insert->getAggregateOperand(), Out, S, Loaded, Via);
        roots(Insert->getInsertedValueOperand(), Out, S, Loaded, Via);
      } else if (const auto *CB = dyn_cast<llvm::CallBase>(O)) {
        const llvm::Function *F = calleeOf(*CB);
        const FunctionDecl *FD = F ? Fns.find(F)->second.FD : nullptr;
        // A function that the compiler wrote and a runtime function with no declaration are known.
        // So is an allocation function, which returns new memory that no other name reaches.
        const bool Known = !F || !FD || !F->isDeclaration() || F->isIntrinsic() || F->returnDoesNotAlias() ||
                           FD->isReplaceableGlobalAllocationFunction() ||
                           ((inStdNamespace(FD) || inAbiNamespace(FD)) && Ctx->getSourceManager().isInSystemHeader(FD->getLocation()));
        if (!Known) {
          Out.push_back({Root::Refuse, O,
                         "global_state: a reference from " + (FD ? FD->getNameAsString() : F->getName().str()) +
                             " may reach any global, and no line can list it."});
          continue;
        }
        for (const llvm::Value *A : CB->args())
          if (A->getType()->isPointerTy())
            roots(A, Out, S, Loaded, Via);
      } else {
        Out.push_back({Root::Refuse, O, ""});
      }
    }
  }

  void call(const llvm::CallBase &CB, Effect &E, Calls *D) {
    // ponytail: an inline assembly call brings nothing. The row inline_asm_intrinsics bans it, and no line could list what it does.
    if (CB.isInlineAsm())
      return;
    if (const auto *Mem = dyn_cast<llvm::MemIntrinsic>(&CB)) {
      access(Mem->getRawDest(), true, E);
      if (const auto *Copy = dyn_cast<llvm::MemTransferInst>(Mem))
        access(Copy->getRawSource(), false, E);
      return;
    }
    if (const llvm::Function *F = calleeOf(CB)) {
      direct(F, CB, E, D);
      return;
    }
    // An indirect call. First the virtual calls that the tree wrote at this place.
    // A method that has a body here brings its lines.
    // One that has none is read as a function with no body, as a direct call of it is.
    // It brings its lines, or it is refused when it has none.
    // ponytail: a virtual call brings the lines of the method that the source names.
    // The checks of overrides hold the overrides of this file to them, the ones with lines and the ones that nobody wrote.
    // An override in another file is not read. Upgrade: read every override of the hierarchy that the file can see.
    const auto &Calls = matched(CB);
    for (const VirtualCall *V : Calls) {
      arguments(V->Method, CB, E);
      E.add(hasBody(V->Method) ? linesOf(V->Method) : edge(V->Method));
      overridden(V->Method, E, D);
    }
    if (!Calls.empty())
      return;
    // A dispatch through a table that no virtual call of the tree explains has no callee that the gate can read.
    // A call through a pointer to a member function is one.
    if (!dispatchesOf(CB).empty()) {
      E.Refusals.insert("global_state: a call through a pointer has no callee the gate can read.");
      return;
    }
    // Else a function that the caller passed, which the caller has accounted for, or a function that the callee value names.
    // A function that is loaded out of an object that a parameter or a local holds counts as passed, as every loaded pointer does. That is
    // sound because whoever stored the function address brought what the function does, `named` above.
    std::vector<Root> Rs;
    Seen S;
    roots(CB.getCalledOperand(), Rs, S);
    for (const Root &R : Rs) {
      if (R.K == Root::Func)
        direct(cast<llvm::Function>(R.V), CB, E, D);
      else if (R.K == Root::Local && isa<llvm::GlobalVariable>(R.V))
        table(cast<llvm::GlobalVariable>(R.V), CB, E, D);
      else if (R.K != Root::Local) {
        E.Refusals.insert("global_state: a call through a pointer has no callee the gate can read.");
      }
    }
  }

  // A call through a pointer that is loaded from a global of the library. The library visits a variant through a table of function
  // pointers. The table is a constant, so the call may run any function that it names.
  // A global with no initializer in the module names none, and the call is refused.
  // This is for the indirect call only. A table of virtual functions is a constant too.
  // The store of its address in a constructor must not bring every virtual function to the constructor.
  void table(const llvm::GlobalVariable *G, const llvm::CallBase &CB, Effect &E, Calls *D) {
    if (!G->hasInitializer()) {
      E.Refusals.insert("global_state: a call through a pointer has no callee the gate can read.");
      return;
    }
    std::vector<const llvm::Function *> Functions;
    llvm::SmallPtrSet<const llvm::Constant *, 16> Done;
    functionsIn(G->getInitializer(), Functions, Done);
    for (const llvm::Function *F : Functions)
      direct(F, CB, E, D);
  }

  // What a virtual call brings besides the lines of the method that the source names.
  // It brings the code of the method, if nobody wrote it. The destructor that the compiler wrote is one, and it has no lines.
  // If a system header declares the method, no line can be asked of the library. Then it brings the code of every override in the module.
  // Every override is a body that the call may run, for the sequencing check.
  // ponytail: every override in the module counts, not only the ones that the object could be. Upgrade: follow the type of the object.
  void overridden(const CXXMethodDecl *Method, Effect &E, Calls *D) {
    const CXXMethodDecl *Canonical = cast<CXXMethodDecl>(Method->getCanonicalDecl());
    if (D)
      for (const llvm::Function *F : Overriders.lookup(Canonical))
        D->Bodies.push_back(F);
    if (const auto Own = ByDecl.find(Canonical); Own != ByDecl.end() && Fns.find(Own->second)->second.Is == Role::Carrier)
      bring(Own->second, E, D);
    if (Ctx->getSourceManager().isInSystemHeader(Method->getLocation()))
      for (const llvm::Function *F : Overriders.lookup(Canonical))
        bring(F, E, D);
  }

  void direct(const llvm::Function *F, const llvm::CallBase &CB, Effect &E, Calls *D) {
    if (F->isIntrinsic())
      return;
    const Fn &Info = Fns.find(F)->second;
    // The compiler's own runtime has no declaration, so no parameter to bind an argument to. With no body it brings nothing, and with one
    // it brings what its own code does.
    // ponytail: a function with a body and no declaration is trusted to touch no state through its arguments.
    if (!Info.FD) {
      if (!F->isDeclaration())
        bring(F, E, D);
      return;
    }
    arguments(Info.FD, CB, E);
    bring(F, E, D);
  }

  // The pointers a call is given. One that reaches a global writes it if the parameter it binds to can write, and reads it if not.
  void arguments(const FunctionDecl *FD, const llvm::CallBase &CB, Effect &E) {
    llvm::SmallVector<bool, 8> Mutable;
    if (FD) {
      if (const auto *Method = dyn_cast<CXXMethodDecl>(FD); Method && !Method->isStatic())
        Mutable.push_back(!Method->isConst());
      for (const ParmVarDecl *Parameter : FD->parameters())
        Mutable.push_back(isMutableType(Parameter->getType()));
    }
    // The arguments that the IR adds are no parameter.
    llvm::SmallVector<unsigned, 8> Real;
    for (unsigned I = 0; I < CB.arg_size(); ++I)
      if (!CB.paramHasAttr(I, llvm::Attribute::StructRet) && !CB.paramHasAttr(I, llvm::Attribute::InAlloca))
        Real.push_back(I);
    // ponytail: the arguments match the parameters in order. A parameter that the ABI splits in two, such as a std::span, or an argument
    // that is a variable argument, throws the order off. Then every pointer is as mutable as the most mutable parameter. Upgrade:
    // read the ABI's own list of arguments from clang.
    const bool Match = Real.size() == Mutable.size();
    const bool Any = llvm::any_of(Mutable, [](bool B) { return B; });
    for (unsigned K = 0; K < Real.size(); ++K) {
      const llvm::Value *A = CB.getArgOperand(Real[K]);
      // An argument by value is a copy, so it is no name.
      if (CB.paramHasAttr(Real[K], llvm::Attribute::ByVal) || !A->getType()->isPointerTy())
        continue;
      std::vector<Root> Rs;
      Seen S;
      roots(A, Rs, S);
      for (const Root &R : Rs)
        reach(R, Match ? Mutable[K] : Any, E);
    }
  }

  // ------------------------------------------------------------ places

  // Where an instruction is, from the debug line table. No file when it has no place.
  Place placeOf(const llvm::Instruction &I) {
    const llvm::DebugLoc &DL = I.getDebugLoc();
    if (!DL || !DL.getLine())
      return {};
    const llvm::DIFile *File = DL->getFile();
    auto Found = Files.find(File);
    if (Found == Files.end()) {
      llvm::SmallString<256> Path(File->getFilename());
      if (!llvm::sys::path::is_absolute(Path))
        Path = (File->getDirectory() + "/" + File->getFilename()).str();
      const auto Entry = Ctx->getSourceManager().getFileManager().getOptionalFileRef(Path);
      Found = Files.try_emplace(File, Entry ? &Entry->getFileEntry() : nullptr).first;
    }
    return {Found->second, DL.getLine(), DL.getCol() ? DL.getCol() : 1};
  }

  // Where an instruction is in the tree: the debug line table, turned back into a location. An instruction with no place is at its
  // function.
  SourceLocation locationOf(const llvm::Instruction &I, const FunctionDecl *FD) {
    if (const Place P = placeOf(I); P.File) {
      const SourceLocation Loc = Ctx->getSourceManager().translateFileLineCol(P.File, P.Line, P.Col);
      if (Loc.isValid())
        return Loc;
    }
    return FD ? FD->getLocation() : SourceLocation();
  }

  // ------------------------------------------------------------ plain code, decision 0047

  // A function of the file, for the gate's kinds: one it defines, and the call operator of a lambda it writes. Such a function has its own
  // kind and its own calls, so a walk from a call stops at it. Anything else in the module is code the file did not write, and a walk
  // goes through it: the library, and the members that the compiler writes.
  bool written(const Fn &Info) const {
    if (Info.Is == Role::Judged)
      return true;
    const auto *Method = dyn_cast_or_null<CXXMethodDecl>(Info.FD);
    return Info.Is == Role::Carrier && Method && isLambdaCallOperator(Method) && !Ctx->getSourceManager().isInSystemHeader(Method->getLocation());
  }

  // The functions that an instruction names, in the module: the callee of a direct call, each function that a virtual call can reach, and
  // each function constant among the operands, as a table of function pointers is. This is what `instruction` and `call` bring, as a
  // list of functions.
  // A virtual call reaches the method that the source names, and every override in the module: one that the file wrote, one that the
  // compiler wrote, such as the destructor of a derived class, and one of a class template over a base that it takes as a parameter.
  // ponytail: a virtual call inside the library has no call in the tree, so the overrides it can reach are not read. Upgrade: the type of
  // the object.
  void namedBy(const llvm::Instruction &I, std::vector<const llvm::Function *> &Out) {
    llvm::SmallPtrSet<const llvm::Constant *, 8> Done;
    const auto *CB = dyn_cast<llvm::CallBase>(&I);
    for (const llvm::Use &U : I.operands())
      if (const auto *C = dyn_cast<llvm::Constant>(U.get()); C && !(CB && &U == &CB->getCalledOperandUse() && calleeOf(*CB)))
        functionsIn(C, Out, Done);
    if (!CB || CB->isInlineAsm() || isa<llvm::MemIntrinsic>(CB))
      return;
    if (const llvm::Function *F = calleeOf(*CB)) {
      if (!F->isIntrinsic())
        Out.push_back(F);
      return;
    }
    const auto &Virtual = matched(*CB);
    for (const VirtualCall *V : Virtual) {
      const CXXMethodDecl *Canonical = cast<CXXMethodDecl>(V->Method->getCanonicalDecl());
      if (const auto Own = ByDecl.find(Canonical); Own != ByDecl.end())
        Out.push_back(Own->second);
      for (const llvm::Function *F : Overriders.lookup(Canonical))
        Out.push_back(F);
    }
    if (!Virtual.empty() || !dispatchesOf(*CB).empty())
      return;
    std::vector<Root> Rs;
    Seen S;
    roots(CB->getCalledOperand(), Rs, S);
    for (const Root &R : Rs) {
      if (R.K == Root::Func) {
        Out.push_back(cast<llvm::Function>(R.V));
      } else if (const auto *G = dyn_cast<llvm::GlobalVariable>(R.V); R.K == Root::Local && G && G->hasInitializer()) {
        llvm::SmallPtrSet<const llvm::Constant *, 16> Visited;
        functionsIn(G->getInitializer(), Out, Visited);
      }
    }
  }

  // Every call of a function of the file, and of the code that starts the globals, that runs a plain function. A plain function is one
  // that the file defines or declares, or a member that the compiler writes for a plain class, decision 0051. The code in the module that
  // the file did not write is followed until it reaches one. The
  // plain functions that each such piece of code can run are found once, by a fixpoint like the one for the effects.
  void plainCode() {
    llvm::DenseSet<const llvm::Function *> Plain;
    for (const auto &[F, Info] : Fns)
      if (Info.FD && (Info.Is == Role::Edge || written(Info) || Info.FD->isImplicit()) &&
          insidePlain(Info.FD->getDefinition() ? Info.FD->getDefinition() : Info.FD))
        Plain.insert(F);
    if (Plain.empty())
      return;
    struct Runs {
      std::set<const llvm::Function *> Plain, Next;
    };
    llvm::DenseMap<const llvm::Function *, Runs> Of;
    std::vector<const llvm::Function *> Named;
    for (const auto &[F, Info] : Fns) {
      if (Info.Is != Role::Carrier || written(Info))
        continue;
      Runs &R = Of[F];
      for (const llvm::BasicBlock &BB : *F)
        for (const llvm::Instruction &I : BB) {
          Named.clear();
          namedBy(I, Named);
          for (const llvm::Function *G : Named) {
            const Fn &Callee = Fns.find(G)->second;
            if (Plain.count(G))
              R.Plain.insert(G);
            else if (Callee.Is == Role::Carrier && !written(Callee))
              R.Next.insert(G);
          }
        }
    }
    for (bool Changed = true; Changed;) {
      Changed = false;
      for (auto &[F, R] : Of)
        for (const llvm::Function *Dep : R.Next)
          if (Dep != F) {
            const auto &Up = Of.find(Dep)->second.Plain;
            const size_t Before = R.Plain.size();
            R.Plain.insert(Up.begin(), Up.end());
            Changed |= R.Plain.size() != Before;
          }
    }
    // The code that starts the globals has no declaration, and it runs what the file wrote.
    for (const auto &[F, Info] : Fns) {
      if (Info.Is == Role::Edge || !(written(Info) || !Info.FD))
        continue;
      for (const llvm::BasicBlock &BB : *F)
        for (const llvm::Instruction &I : BB) {
          Named.clear();
          namedBy(I, Named);
          for (const llvm::Function *G : Named) {
            if (Plain.count(G))
              plainCall(I, Info.FD, G);
            else if (const auto Up = Of.find(G); Up != Of.end())
              for (const llvm::Function *P : Up->second.Plain)
                plainCall(I, Info.FD, P);
          }
        }
    }
  }

  // The code that starts a global has no place of its own, so its call stands at the variable that it starts.
  // ponytail: the first variable of the user's files that the code names. Upgrade: the variable that the call is for.
  SourceLocation globalStarted(const llvm::Function &F) const {
    for (const llvm::BasicBlock &BB : F)
      for (const llvm::Instruction &I : BB)
        for (const llvm::Use &U : I.operands())
          if (const auto *G = dyn_cast<llvm::GlobalVariable>(U.get()))
            if (const auto Var = VarOf.find(G); Var != VarOf.end() && !Ctx->getSourceManager().isInSystemHeader(Var->second->getLocation()))
              return Var->second->getLocation();
    return {};
  }

  // Where a call of a function of the file stands, as a place in a file. None when the call has no place.
  SourceLocation callPlace(const llvm::Instruction &I, const FunctionDecl *Holder) {
    SourceLocation Loc = locationOf(I, Holder);
    if (Loc.isInvalid() && !Holder)
      Loc = globalStarted(*I.getFunction());
    return Loc.isInvalid() ? Loc : Ctx->getSourceManager().getExpansionLoc(Loc);
  }

  void plainCall(const llvm::Instruction &I, const FunctionDecl *Holder, const llvm::Function *Plain) {
    const SourceLocation At = callPlace(I, Holder);
    if (At.isInvalid())
      return;
    const std::string Name = patternOf(Fns.find(Plain)->second.FD)->getQualifiedNameAsString();
    if (PlainSeen.insert({At.getRawEncoding(), Name}).second)
      PlainCalls.push_back({At, Name});
  }

  // ------------------------------------------------------------ indirect calls, decisions 0048 and 0049

  // Whether the contents of a piece of memory are named: the pointer is read from a constant table, or from a local object that holds
  // nothing but named values. Memory that a parameter, a call or a global that can change gives has no name.
  // A call of code that the file did not write can hand out a place in a table that its caller gave, as the library does to find the
  // function for a pair of variants. The place is then the one that the call was given: the pointer that it returns comes from its
  // parameter or from a constant table, and the walk follows it into the call. `Frames` are the calls that the walk is inside.
  bool namesMemory(const llvm::Value *Pointer, llvm::SmallPtrSetImpl<const llvm::Value *> &Done,
                   llvm::SmallVectorImpl<const llvm::CallBase *> &Frames) {
    llvm::SmallVector<const llvm::Value *, 4> Objects;
    llvm::getUnderlyingObjects(Pointer, Objects, nullptr, 0);
    for (const llvm::Value *O : Objects) {
      if (const auto *G = dyn_cast<llvm::GlobalVariable>(O)) {
        if (!G->isConstant() || !G->hasInitializer())
          return false;
      } else if (isa<llvm::AllocaInst>(O)) {
        if (!Frames.empty() || (Done.insert(O).second && !namesLocal(O, Done)))
          return false;
      } else if (const auto *Parameter = dyn_cast<llvm::Argument>(O)) {
        if (Frames.empty())
          return false;
        const llvm::CallBase *Call = Frames.pop_back_val();
        const bool Named = namesMemory(Call->getArgOperand(Parameter->getArgNo()), Done, Frames);
        Frames.push_back(Call);
        if (!Named)
          return false;
      } else if (const auto *Call = dyn_cast<llvm::CallBase>(O)) {
        const llvm::Function *Callee = calleeOf(*Call);
        if (!Callee || Callee->isDeclaration() || written(Fns.find(Callee)->second) || !Done.insert(Call).second)
          return false;
        Frames.push_back(Call);
        for (const llvm::BasicBlock &BB : *Callee)
          if (const auto *Ret = dyn_cast<llvm::ReturnInst>(BB.getTerminator()))
            if (!Ret->getReturnValue() || !namesMemory(Ret->getReturnValue(), Done, Frames))
              return false;
        Frames.pop_back();
      } else {
        return false;
      }
    }
    return true;
  }

  // Whether a local object holds named values only. Every store into it and every copy into it brings a named value. Its address stays
  // here: a call that gets the address can store any pointer in it, and so can anything that keeps the address.
  bool namesLocal(const llvm::Value *Slot, llvm::SmallPtrSetImpl<const llvm::Value *> &Done) {
    llvm::SmallVector<const llvm::CallBase *, 1> NoFrames;
    llvm::SmallVector<const llvm::Value *, 8> Work{Slot};
    llvm::SmallPtrSet<const llvm::Value *, 8> Derived{Slot};
    while (!Work.empty()) {
      const llvm::Value *P = Work.pop_back_val();
      for (const llvm::User *U : P->users()) {
        if (isa<llvm::LoadInst, llvm::ICmpInst>(U))
          continue;
        if (const auto *Store = dyn_cast<llvm::StoreInst>(U)) {
          if (Store->getValueOperand() == P || !namesAll(Store->getValueOperand(), Done))
            return false;
        } else if (const auto *Copy = dyn_cast<llvm::MemTransferInst>(U)) {
          if (Copy->getRawDest() == P && !namesMemory(Copy->getRawSource(), Done, NoFrames))
            return false;
        } else if (const auto *Intrinsic = dyn_cast<llvm::IntrinsicInst>(U)) {
          if (!isa<llvm::MemSetInst, llvm::DbgInfoIntrinsic>(Intrinsic) && !Intrinsic->isLifetimeStartOrEnd())
            return false;
        } else if (isa<llvm::GetElementPtrInst, llvm::BitCastInst, llvm::AddrSpaceCastInst, llvm::PHINode, llvm::SelectInst>(U)) {
          if (Derived.insert(U).second)
            Work.push_back(U);
        } else {
          return false;
        }
      }
    }
    return true;
  }

  // Whether each value that can reach `V` is named, decision 0049: a function constant, or a pointer read from memory that is named. A
  // parameter, `this`, the result of a call, a return slot and a pointer of a global that can change have no name. A virtual call and a
  // table of decision 0037 are named by their vtables and their constants, and the caller does not ask about them.
  bool namesAll(const llvm::Value *V, llvm::SmallPtrSetImpl<const llvm::Value *> &Done) {
    llvm::SmallVector<const llvm::Value *, 4> Objects;
    llvm::getUnderlyingObjects(V, Objects, nullptr, 0);
    for (const llvm::Value *O : Objects) {
      if (!Done.insert(O).second)
        continue;
      if (isa<llvm::Constant>(O) && !isa<llvm::GlobalVariable>(O))
        continue;
      if (const auto *Load = dyn_cast<llvm::LoadInst>(O)) {
        llvm::SmallVector<const llvm::CallBase *, 4> Frames;
        if (!namesMemory(Load->getPointerOperand(), Done, Frames))
          return false;
      } else if (const auto *Extract = dyn_cast<llvm::ExtractValueInst>(O)) {
        if (!namesAll(Extract->getAggregateOperand(), Done))
          return false;
      } else if (const auto *Insert = dyn_cast<llvm::InsertValueInst>(O)) {
        if (!namesAll(Insert->getAggregateOperand(), Done) || !namesAll(Insert->getInsertedValueOperand(), Done))
          return false;
      } else if (const auto *Cast = dyn_cast<llvm::IntToPtrInst>(O)) {
        if (!namesAll(Cast->getOperand(0), Done))
          return false;
      } else {
        return false;
      }
    }
    return true;
  }

  // An indirect call that is no virtual call, and that has no name. The dispatch of a virtual call reads a vtable, and the tree names the
  // method. A dispatch that no call of the tree explains is a pointer to a member function, which the row already refuses.
  bool unnamedCall(const llvm::CallBase &CB) {
    if (CB.isInlineAsm() || isa<llvm::MemIntrinsic>(CB) || calleeOf(CB) || !matched(CB).empty() || !dispatchesOf(CB).empty())
      return false;
    llvm::SmallPtrSet<const llvm::Value *, 16> Done;
    return !namesAll(CB.getCalledOperand(), Done);
  }

  // Every call of a function of the file, and of the code that starts the globals, that runs an indirect call with no name. It makes the
  // call itself, or it runs code that the file did not write and that makes it. The row `function_pointers` judges that call. A pointer
  // is named by constants alone, so a pointer that a parameter holds, or a call gave, or a call can write, has no name, and a verified
  // function that calls through it is refused. A trusted body may hold such a pointer, and the core drops the finding there.
  // ponytail: the walk of a local object reads its stores and its copies. Any other use of the address is a call, and the object has no
  // name from then on, whatever the call does with it. A pointer in a global that can change has no name either. Upgrade: read what the
  // call may store, from the lowered form of its body.
  void indirectCode() {
    // The code that the file did not write and that has an unnamed indirect call, by a fixpoint like the one for the plain functions.
    llvm::DenseSet<const llvm::Function *> Unnamed;
    llvm::DenseMap<const llvm::Function *, std::vector<const llvm::Function *>> Next;
    std::vector<const llvm::Function *> Named;
    for (const auto &[F, Info] : Fns) {
      if (Info.Is != Role::Carrier || written(Info))
        continue;
      auto &Mine = Next[F];
      for (const llvm::BasicBlock &BB : *F)
        for (const llvm::Instruction &I : BB) {
          if (const auto *CB = dyn_cast<llvm::CallBase>(&I); CB && unnamedCall(*CB))
            Unnamed.insert(F);
          Named.clear();
          namedBy(I, Named);
          for (const llvm::Function *G : Named)
            if (const Fn &Callee = Fns.find(G)->second; Callee.Is == Role::Carrier && !written(Callee))
              Mine.push_back(G);
        }
    }
    for (bool Changed = true; Changed;) {
      Changed = false;
      for (const auto &[F, Callees] : Next)
        if (!Unnamed.count(F) && llvm::any_of(Callees, [&](const llvm::Function *G) { return Unnamed.count(G); }))
          Changed |= Unnamed.insert(F).second;
    }
    for (const auto &[F, Info] : Fns) {
      if (Info.Is == Role::Edge || !(written(Info) || !Info.FD))
        continue;
      for (const llvm::BasicBlock &BB : *F)
        for (const llvm::Instruction &I : BB) {
          const auto *CB = dyn_cast<llvm::CallBase>(&I);
          bool Found = CB && unnamedCall(*CB);
          if (!Found) {
            Named.clear();
            namedBy(I, Named);
            Found = llvm::any_of(Named, [&](const llvm::Function *G) { return Unnamed.count(G); });
          }
          if (!Found)
            continue;
          if (const SourceLocation At = callPlace(I, Info.FD); At.isValid() && IndirectSeen.insert(At.getRawEncoding()).second)
            IndirectCalls.push_back(At);
        }
    }
  }

  // ------------------------------------------------------------ judging

  // The function is judged on its own instructions, against its own lines. The module may hold it twice, as the variants of a constructor
  // or a destructor are, and each is judged. `Reported` keeps one finding for a line and a message.
  void judge(const llvm::Function &F, const FunctionDecl *FD) {
    const SourceManager &SM = Ctx->getSourceManager();
    const Effect Own = linesOf(FD);
    enum Kind { Write, Read, Refusal };
    struct Item {
      SourceLocation Loc;
      Kind K;
      std::string Text;
    };
    std::vector<Item> Items;
    for (const llvm::BasicBlock &BB : F)
      for (const llvm::Instruction &I : BB) {
        Effect E;
        instruction(I, E, nullptr);
        if (!E.size())
          continue;
        const SourceLocation Loc = locationOf(I, FD);
        for (const std::string &Name : E.Writes)
          if (!Own.Writes.count(Name))
            Items.push_back({Loc, Write, Name});
        for (const std::string &Name : E.Reads)
          if (!Own.Writes.count(Name) && !Own.Reads.count(Name))
            Items.push_back({Loc, Read, Name});
        for (const std::string &Message : E.Refusals)
          Items.push_back({Loc, Refusal, Message});
      }
    const auto Line = [&](SourceLocation Loc) { return std::make_pair(SM.getFileID(Loc).getHashValue(), SM.getExpansionLineNumber(Loc)); };
    // Where a line writes a name and reads it too, the write is the finding.
    std::set<std::pair<std::pair<unsigned, unsigned>, std::string>> Written;
    for (const Item &It : Items)
      if (It.K == Write)
        Written.insert({Line(It.Loc), It.Text});
    for (const Item &It : Items) {
      if (It.K == Read && Written.count({Line(It.Loc), It.Text}))
        continue;
      const std::string Message = It.K == Write  ? "global_state: " + It.Text + " changes, and the modifies line does not list it."
                                  : It.K == Read ? "global_state: " + It.Text + " is read, and no reads or modifies line lists it."
                                                 : It.Text;
      report(It.Loc, Message);
    }
  }
};

// One table for the translation unit. It is never freed at exit: the libraries it holds may be gone by then.
Lowered *Table = nullptr;
// Whether some check has asked for the matchers of the table in this translation unit. One does, whichever checks are on.
bool TableMatchers = false;
Lowered &table() {
  if (!Table)
    Table = new Lowered;
  return *Table;
}
void startTable() {
  delete Table;
  Table = nullptr;
  TableMatchers = false;
}
bool tableChanges(const FunctionDecl *Callee) { return table().changes(Callee); }
void giveTable(ASTContext *Context) { table().use(Context); }

// The method that a call or a delete reaches through the vtable, as the source says it, or null.
const CXXMethodDecl *virtualTarget(const Stmt *S) {
  if (const auto *Call = dyn_cast<CallExpr>(S)) {
    const auto *Method = dyn_cast_or_null<CXXMethodDecl>(Call->getCalleeDecl());
    // A call with a qualifier names the function, and the call is no virtual one.
    const auto *Member = dyn_cast<MemberExpr>(Call->getCallee()->IgnoreParens());
    return Method && Method->isVirtual() && !(Member && Member->hasQualifier()) ? Method : nullptr;
  }
  if (const auto *Delete = dyn_cast<CXXDeleteExpr>(S)) {
    // A delete of an object with a virtual destructor calls it through the vtable.
    const QualType Destroyed = Delete->getDestroyedType();
    const CXXRecordDecl *Class = Destroyed.isNull() ? nullptr : Destroyed->getAsCXXRecordDecl();
    const CXXDestructorDecl *Destructor = Class && Class->hasDefinition() ? Class->getDestructor() : nullptr;
    return Destructor && Destructor->isVirtual() ? Destructor : nullptr;
  }
  return nullptr;
}

// The virtual calls inside a default argument. The compiler puts the code of a default argument on the line of the call that uses it.
// So they are recorded with the range of that call, and the function that holds that call.
void collectDefault(const Stmt *S, SourceRange Where, const FunctionDecl *Owner) {
  if (!S)
    return;
  if (const CXXMethodDecl *Method = virtualTarget(S))
    table().addVirtual(Where, Method, Owner);
  if (const auto *Default = dyn_cast<CXXDefaultArgExpr>(S))
    collectDefault(Default->getExpr(), Where, Owner);
  else if (const auto *Init = dyn_cast<CXXDefaultInitExpr>(S))
    collectDefault(Init->getExpr(), Where, Owner);
  else
    for (const Stmt *Child : S->children())
      collectDefault(Child, Where, Owner);
}

void registerTableMatchers(MatchFinder *Finder, MatchFinder::MatchCallback *Callback) {
  if (TableMatchers)
    return;
  TableMatchers = true;
  // The function that holds the expression, which tells the same line of two functions apart. A default member initializer has none: its
  // code runs in every function that makes the object.
  const auto Holder = optionally(allOf(unless(hasAncestor(fieldDecl())), forFunction(functionDecl().bind("owner"))));
  const auto Defaulted = hasAnyArgument(ignoringImplicit(cxxDefaultArgExpr()));
  Finder->addMatcher(functionDecl(isDefinition(), unless(isExpansionInSystemHeader()), unless(notJudged())).bind("judged"), Callback);
  Finder->addMatcher(functionDecl(isDefinition(), isTemplateInstantiation()).bind("instance"), Callback);
  Finder->addMatcher(varDecl(isDefinition(), hasGlobalStorage(), isTemplateInstantiation()).bind("varinstance"), Callback);
  Finder->addMatcher(stmt(anyOf(callExpr(callee(cxxMethodDecl(isVirtual()))), cxxDeleteExpr()), Holder).bind("virtual"), Callback);
  Finder->addMatcher(stmt(anyOf(callExpr(Defaulted), cxxConstructExpr(Defaulted)), Holder).bind("defaulted"), Callback);
}

bool collectForTable(const MatchFinder::MatchResult &Result) {
  Lowered &T = table();
  const SourceManager &SM = *Result.SourceManager;
  const auto *Owner = Result.Nodes.getNodeAs<FunctionDecl>("owner");
  if (const auto *Function = Result.Nodes.getNodeAs<FunctionDecl>("judged")) {
    T.Judged.push_back(Function);
  } else if (const auto *Function = Result.Nodes.getNodeAs<FunctionDecl>("instance")) {
    T.Instances.push_back(Function);
  } else if (const auto *Var = Result.Nodes.getNodeAs<VarDecl>("varinstance")) {
    T.VarInstances.push_back(Var);
  } else if (const auto *Node = Result.Nodes.getNodeAs<Stmt>("virtual")) {
    if (const CXXMethodDecl *Method = virtualTarget(Node))
      T.addVirtual(SM.getExpansionRange(Node->getSourceRange()).getAsRange(), Method, Owner);
  } else if (const auto *Node = Result.Nodes.getNodeAs<Stmt>("defaulted")) {
    const SourceRange Where = SM.getExpansionRange(Node->getSourceRange()).getAsRange();
    const auto Each = [&](auto Arguments) {
      for (const Expr *Argument : Arguments)
        if (const auto *Default = dyn_cast<CXXDefaultArgExpr>(Argument->IgnoreImplicit()))
          collectDefault(Default->getExpr(), Where, Owner);
    };
    if (const auto *Call = dyn_cast<CallExpr>(Node))
      Each(Call->arguments());
    else
      Each(cast<CXXConstructExpr>(Node)->arguments());
  } else {
    return false;
  }
  return true;
}

// cplusp-unlisted-state: decisions 0035, 0036 and 0037. A function writes only the global state its `//@ modifies` line lists.
// It reads only what its `//@ reads` or `modifies` line lists.
// State is a mutable global or static data member that a system header does not declare.
// The check judges the code that clang generates for the function, not the tree.
// A store is a write, a load is a read, and a call brings what its callee lists or what the callee's own code does.
// A call of a function that the gate cannot read is refused. So is a reference from a function this file does not define.
// Any global may be behind it, and no line can list that.
// The message is `global_state: {sentence}`, one finding per message per line.
// The pattern of a template is not judged. Its instantiations are.
class UnlistedStateCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void onStartOfTranslationUnit() override { startTable(); }
  void registerMatchers(MatchFinder *Finder) override {
    // The translation unit, so that the check runs once at least and has the context.
    Finder->addMatcher(translationUnitDecl(), this);
    registerTableMatchers(Finder, this);
    Finder->addMatcher(cxxMethodDecl(unless(isExpansionInSystemHeader()), unless(isImplicit())).bind("method"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    giveTable(Result.Context);
    if (collectForTable(Result))
      return;
    if (const auto *Method = Result.Nodes.getNodeAs<CXXMethodDecl>("method"))
      if (Method == Method->getCanonicalDecl())
        checkOverride(Method, *Result.SourceManager);
  }
  void onEndOfTranslationUnit() override {
    for (const Finding &F : table().findings())
      diag(F.Loc, "%0") << StringRef(F.Message);
  }

private:
  // An override lists no more than the function it overrides, so that a call through the base brings lines that hold for every override.
  void checkOverride(const CXXMethodDecl *Method, const SourceManager &SM) {
    if (Method->size_overridden_methods() == 0)
      return;
    const Contract Own = contractOf(SM, Method);
    const auto &State = table().state();
    for (const CXXMethodDecl *Direct : Method->overridden_methods())
      for (const CXXMethodDecl *Base : lineHolders(Direct)) {
        const Contract Up = contractOf(SM, Base);
        const std::set<std::string> UpWrites = namedState(Up.Modifies, State, Up.Parameters), UpReads = namedState(Up.Reads, State, Up.Parameters);
        for (const std::string &Var : namedState(Own.Modifies, State, Own.Parameters))
          if (!UpWrites.count(Var))
            diag(Method->getLocation(), "global_state: %0 changes %1, and the modifies line of %2 does not list it.")
                << Method->getNameAsString() << StringRef(Var) << Base->getQualifiedNameAsString();
        for (const std::string &Var : namedState(Own.Reads, State, Own.Parameters))
          if (!UpWrites.count(Var) && !UpReads.count(Var))
            diag(Method->getLocation(), "global_state: %0 reads %1, and no reads or modifies line of %2 lists it.")
                << Method->getNameAsString() << StringRef(Var) << Base->getQualifiedNameAsString();
      }
  }
};

// cplusp-line-directive: decision 0037. Every `#line` and every line marker that the preprocessor processed, under the build's own flags.
// The preprocessor holds them in the line table of the source manager.
// The entry sits in the directive's line. So the finding sits at the first column of that line, before the directive.
// A marker may declare the rest of its file a system header, which clang-tidy does not judge.
// The entry that `#pragma GCC system_header` adds is no directive. The check `cplusp-pragma` reports the pragma.
// The preprocessor tells where it made one. No other entry is skipped, so `# 3 "this file" 3` is a finding.
// A NOLINT on the line of a directive suppresses this finding. The gate reports the NOLINT, and that stands.
// ponytail: the entry sits on the line of the number. A directive that a comment spreads over lines is reported on the line of its
// number, not of its `#`. Upgrade: a callback of the preprocessor for each directive.
class LineDirectiveCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void registerMatchers(MatchFinder *Finder) override { Finder->addMatcher(translationUnitDecl(), this); }
  void registerPPCallbacks(const SourceManager &, Preprocessor *PP, Preprocessor *) override {
    // The gate runs one clang-tidy over every file, and each unit has its own offsets.
    Pragmas.clear();
    PP->addPPCallbacks(std::make_unique<PragmaNotes>(Pragmas));
  }
  void check(const MatchFinder::MatchResult &Result) override { SM = Result.SourceManager; }
  void onEndOfTranslationUnit() override {
    LineTableInfo &Lines = SM->getLineTable();
    for (const auto &[File, Entries] : Lines) {
      // The predefined macros are a buffer that holds line markers of its own, and no file of the user's.
      if (!SM->getFileEntryForID(File))
        continue;
      const StringRef Text = SM->getBufferData(File);
      const auto Offset = [&](unsigned Line) { return SM->getFileOffset(SM->translateLineCol(File, Line, 1)); };
      for (const LineEntry &Entry : Entries) {
        unsigned Line = SM->getLineNumber(File, Entry.FileOffset);
        const SourceLocation Own = SM->translateLineCol(File, Line, 1);
        if (SM->isInSystemHeader(Own) || Pragmas.count(SM->getLocForStartOfFile(File).getLocWithOffset(Entry.FileOffset).getRawEncoding()))
          continue;
        // A line splice joins the lines of a directive, and the `#` is on the first of them.
        while (Line > 1 && Text.slice(Offset(Line - 1), Offset(Line)).rtrim().ends_with("\\"))
          --Line;
        diag(SM->translateLineCol(File, Line, 1), "line directive: not allowed in verified code. It moves the gate's view.");
      }
    }
  }

private:
  // Where the preprocessor made a line table entry for a `system_header` pragma.
  struct PragmaNotes : PPCallbacks {
    std::set<SourceLocation::UIntTy> &Where;
    explicit PragmaNotes(std::set<SourceLocation::UIntTy> &Where) : Where(Where) {}
    void FileChanged(SourceLocation Loc, FileChangeReason Reason, SrcMgr::CharacteristicKind, FileID) override {
      if (Reason == SystemHeaderPragma)
        Where.insert(Loc.getRawEncoding());
    }
  };
  SourceManager *SM = nullptr;
  std::set<SourceLocation::UIntTy> Pragmas;
};

// A finding of the gate's own at `At`, which is a place in a file. The message is the presumed place, then the sentence, set apart by tabs.
// The pragma check and the marker check report this way. The gate reads the line from the message and maps the finding to its rule.
// A tab or a line break in the sentence would move the cut of the gate, so each becomes a space. A sentence can hold the text of the source.
void reportAt(ClangTidyCheck &Check, const SourceManager &SM, SourceLocation At, const std::string &Sentence) {
  const PresumedLoc Place = SM.getPresumedLoc(At);
  std::string Clean = Sentence;
  std::replace_if(Clean.begin(), Clean.end(), [](char C) { return C == '\t' || C == '\n' || C == '\r'; }, ' ');
  if (Place.isValid())
    Check.diag(At, "%0") << StringRef(std::string(Place.getFilename()) + "\t" + std::to_string(Place.getLine()) + "\t" + Clean);
}

// cplusp-pragma: decision 0038. Every `#pragma`, `_Pragma` and `__pragma` that the preprocessor reads, under the build's own flags.
// It also refuses a header name with a backslash. The compiler reads such a name its own way, and the dependency list prints it as a slash.
// The preprocessor says when it starts one, before any handler runs. So a raw string that looks like a pragma is no pragma.
// The gate reads no compiler output that holds source text. A pragma in a system header is the library's own.
// The finding of a `#pragma` sits at the end of its first word, in the file that holds it. The pragma's own line is still a user line.
// A header turns system from the next line on, and that is after this callback.
// A `system_header` pragma in the main file is a finding too. Clang ignores it there, and it is still not allowed.
// The message is the presumed file, the presumed line and the sentence for the bot, set apart by tabs.
// A `#line` moves the presumed place, and the finding shows the place that the author gave.
// A NOLINT on the line of a pragma or an include suppresses the finding of this check. The gate reports the NOLINT, and that stands.
// A diagnostic pragma in a system header may change the warnings of the code that includes it.
// The compiler keeps the state of every warning, with its pushes and pops. So the check asks it, and keeps no count of its own.
// The preprocessor enters a system header from a file that is none. The check asks the level of each warning that the policy enforces,
// at the include. The header ends and the file resumes. The check asks again at the place where the file resumes.
// A warning that was on and is off is the finding. User code cannot change a warning, because every pragma in it is refused.
// The finding sits at the include that brought the outermost header in.
// When that include is no file, as with `-include`, it sits at the start of the main file.
// A header that pushes and pops around its change, as libstdc++ does, stays quiet.
// ponytail: the words come from the source, read by the compiler's lexer at the introducer. A `__pragma` expands macros first.
// So the words of a `__pragma` may not be the ones that run. Only a `#pragma` is `once` for the gate, which reads no more than that.
// The diagnostic pragmas that run are reported by their own callbacks, whatever the words said. Another pragma that a macro makes
// is still a finding, and its sentence names the source words. Upgrade: read the tokens that the handler reads.
// Reading them ahead with a backtrack in the callback changes the build. A macro in the pragma is no longer expanded.
// A pragma that nobody knows leaves its words to the parser.
class PragmaCheck : public ClangTidyCheck {
public:
  // The base class keeps the context private, so the check keeps its own pointer.
  PragmaCheck(StringRef Name, ClangTidyContext *Context) : ClangTidyCheck(Name, Context), Ctx(Context) {}
  void registerPPCallbacks(const SourceManager &SM, Preprocessor *PP, Preprocessor *) override {
    // The driver turns `-include h.h` into `-include-pch h.h.pch` when that file sits beside the header. The compiler tells it.
    if (!PP->getPreprocessorOpts().ImplicitPCHInclude.empty())
      refusePrecompiled(*this, SM);
    PP->addPPCallbacks(std::make_unique<Notes>(*this, *Ctx, SM, *PP));
  }
  void registerMatchers(MatchFinder *Finder) override { Finder->addMatcher(translationUnitDecl(), this); }
  // A precompiled header and a module are read by the AST reader, whichever way the build came to load one.
  // clang-tidy gives every run a reader, and it holds no file until a precompiled header or a module is loaded.
  // An external source of any other kind is refused too.
  void check(const MatchFinder::MatchResult &Result) override {
    ExternalASTSource *Source = Result.Context->getExternalSource();
    if (Source && (!isa<ASTReader>(Source) || cast<ASTReader>(Source)->getModuleManager().size()))
      refusePrecompiled(*this, *Result.SourceManager);
  }

private:
  ClangTidyContext *Ctx;

  // Precompiled state carries what an earlier run of the compiler read, and the gate did not see it. The finding sits at the start of
  // the main file. Both ways of finding it report the same place and the same words, and the diagnostics engine keeps one.
  static void refusePrecompiled(ClangTidyCheck &Check, const SourceManager &SM) {
    reportAt(Check, SM, SM.getLocForStartOfFile(SM.getMainFileID()),
             "include: a precompiled header is loaded. It carries state from an earlier run of the compiler.");
  }

  struct Notes : PPCallbacks {
    ClangTidyCheck &Check;
    ClangTidyContext &Context;
    const SourceManager &SM;
    Preprocessor &PP;
    // Whether the `#pragma` that started last was already reported as a diagnostic pragma, so that its callback does not report it twice.
    bool DiagnosticSeen = false;
    // The files that are being read. A system header entered from a file that is none holds the levels of the warnings.
    // They are the warnings that the policy enforces, as they were at its include.
    struct Frame {
      bool System = false;
      bool Outermost = false;
      std::vector<bool> Enforced;
    };
    std::vector<Frame> Frames;
    unsigned SystemFrames = 0;
    // The warnings that the policy enforces: those whose `clang-diagnostic-{name}` check is on in this run. Found once.
    std::vector<unsigned> Enforced;
    bool EnforcedKnown = false;
    Notes(ClangTidyCheck &Check, ClangTidyContext &Context, const SourceManager &SM, Preprocessor &PP)
        : Check(Check), Context(Context), SM(SM), PP(PP) {}

    void report(SourceLocation At, const std::string &Sentence) { reportAt(Check, SM, At, Sentence); }

    // A diagnostic pragma that the preprocessor runs, whatever words said that it would.
    void diagnostic(SourceLocation Loc) {
      const SourceLocation At = SM.getExpansionLoc(Loc);
      if (!DiagnosticSeen && At.isValid() && !SM.isInSystemHeader(At))
        report(At, "pragma diagnostic: not allowed in verified code. It silences the gate.");
    }

    const std::vector<unsigned> &enforced() {
      if (!EnforcedKnown) {
        EnforcedKnown = true;
        std::vector<diag::kind> All;
        DiagnosticIDs::getAllDiagnostics(diag::Flavor::WarningOrError, All);
        for (const unsigned ID : All) {
          const StringRef Option = DiagnosticIDs::getWarningOptionForDiag(ID);
          if (!Option.empty() && Context.isCheckEnabled(("clang-diagnostic-" + Option).str()))
            Enforced.push_back(ID);
        }
      }
      return Enforced;
    }

    // Which of the warnings that the policy enforces are on at `At`.
    std::vector<bool> levels(SourceLocation At) {
      std::vector<bool> On;
      for (const unsigned ID : enforced())
        On.push_back(PP.getDiagnostics().getDiagnosticLevel(ID, At) != DiagnosticsEngine::Ignored);
      return On;
    }

    // A system header changed the warnings of the code that includes it. The finding sits at the include that brought it in.
    // An include that is no file, as `-include` makes, has no place of its own. Then the finding sits at the start of the main file.
    void leak(FileID Header) {
      SourceLocation Include = SM.getIncludeLoc(Header);
      if (Include.isInvalid() || !SM.getFileEntryForID(SM.getFileID(Include)))
        Include = SM.getLocForStartOfFile(SM.getMainFileID());
      report(SM.getExpansionLoc(Include), "pragma diagnostic: a system header changes the warnings of the code that includes it. It silences the gate.");
    }

    void FileChanged(SourceLocation Loc, FileChangeReason Reason, SrcMgr::CharacteristicKind Kind, FileID Previous) override {
      const bool System = SrcMgr::isSystem(Kind);
      if (Reason == EnterFile) {
        Frame Entered;
        Entered.System = System;
        // A buffer that is no file, as `<built-in>`, holds no header.
        if (System && !SystemFrames && SM.getFileEntryForID(SM.getFileID(Loc))) {
          Entered.Outermost = true;
          Entered.Enforced = levels(SM.getIncludeLoc(SM.getFileID(Loc)));
        }
        SystemFrames += System;
        Frames.push_back(std::move(Entered));
      } else if (Reason == ExitFile && !Frames.empty()) {
        const Frame Ended = std::move(Frames.back());
        Frames.pop_back();
        SystemFrames -= Ended.System;
        if (!Ended.Outermost || System)
          return;
        // The file resumes. A warning that the header found on and that is off here, the header turned off.
        const std::vector<bool> Now = levels(Loc);
        for (size_t I = 0; I < Now.size() && I < Ended.Enforced.size(); ++I)
          if (Ended.Enforced[I] && !Now[I]) {
            leak(Previous);
            return;
          }
      }
    }

    void PragmaDiagnostic(SourceLocation Loc, StringRef, diag::Severity, StringRef) override { diagnostic(Loc); }
    void PragmaDiagnosticPush(SourceLocation Loc, StringRef) override { diagnostic(Loc); }
    void PragmaDiagnosticPop(SourceLocation Loc, StringRef) override { diagnostic(Loc); }

    void InclusionDirective(SourceLocation HashLoc, const Token &, StringRef FileName, bool, CharSourceRange, OptionalFileEntryRef, StringRef,
                            StringRef, const Module *, SrcMgr::CharacteristicKind) override {
      const SourceLocation At = SM.getExpansionLoc(HashLoc);
      if (FileName.contains('\\') && At.isValid() && !SM.isInSystemHeader(At))
        report(At, "include: a header name with a backslash is not allowed in verified code. The compiler may read it as another file.");
    }

    // Where a pragma starts. A `#pragma` starts at its hash, and its words follow the word `pragma`.
    // A `__pragma` starts at its introducer, and its words follow `__pragma(`. The text of a `_Pragma` starts at its words.
    enum class Start { Hash, Microsoft, Text };

    // The words of the pragma that starts at `Where`, with the place of the first one.
    // The compiler's lexer reads them, in raw mode. So a splice, a comment, a digraph and a trigraph are what the build says.
    // The words are the tokens up to a parenthesis.
    // A fresh raw lexer marks its first token as the start of a line. So it starts at the introducer, and the first token is skipped.
    std::vector<std::string> wordsFrom(SourceLocation Where, Start How, SourceLocation &First) const {
      const SourceLocation Spelling = SM.getSpellingLoc(Where);
      const auto [File, Offset] = SM.getDecomposedLoc(Spelling);
      bool Invalid = false;
      const StringRef Buffer = SM.getBufferData(File, &Invalid);
      if (Invalid || Offset > Buffer.size())
        return {};
      const char *Start = Buffer.data() + Offset, *End = Buffer.end();
      // A scratch buffer holds many strings, and each ends at its own null character.
      if (SM.isWrittenInScratchSpace(Spelling)) {
        const size_t Nul = StringRef(Start, Buffer.end() - Start).find('\0');
        if (Nul != StringRef::npos)
          End = Start + Nul;
      }
      Lexer Raw(SM.getLocForStartOfFile(File), PP.getLangOpts(), Buffer.begin(), Start, End);
      std::string Text;
      Token Tok;
      bool FirstToken = true, InIntroducer = How == Start::Hash;
      unsigned Skip = How == Start::Microsoft ? 2 : 0, Budget = 4;
      for (bool AtEnd = false; !AtEnd;) {
        AtEnd = Raw.LexFromRawLexer(Tok);
        if (Tok.is(tok::eof) || (!FirstToken && Tok.isAtStartOfLine()))
          break;
        FirstToken = false;
        if (InIntroducer) {
          // The hash, then `pragma`. Nothing else may stand between them but what the lexer skips.
          if (Lexer::getSpelling(Tok, SM, PP.getLangOpts()) == "pragma")
            InIntroducer = false;
          else if (!--Budget)
            return {};
          continue;
        }
        if (Skip) {
          --Skip;
          continue;
        }
        if (Tok.isOneOf(tok::l_paren, tok::r_paren))
          break;
        // The last character of the word. A splice before the word belongs to the line that the word ends on.
        if (First.isInvalid())
          First = Tok.getLocation().getLocWithOffset(Tok.getLength() ? Tok.getLength() - 1 : 0);
        Text += Lexer::getSpelling(Tok, SM, PP.getLangOpts()) + " ";
      }
      std::vector<std::string> Words;
      std::string Word;
      for (const char C : Text + " ") {
        if (isalnum(static_cast<unsigned char>(C)) || C == '_') {
          Word += C;
        } else if (!Word.empty()) {
          Words.push_back(std::move(Word));
          Word.clear();
        }
      }
      if (Words.size() > 2)
        Words.resize(2);
      return Words;
    }

    void PragmaDirective(SourceLocation Loc, PragmaIntroducerKind Kind) override {
      DiagnosticSeen = false;
      SourceLocation First;
      std::vector<std::string> Words;
      if (Kind == PIK___pragma)
        Words = wordsFrom(Loc, Start::Microsoft, First);
      else if (Kind == PIK_HashPragma)
        Words = wordsFrom(Loc, Start::Hash, First);
      else if (PreprocessorLexer *Current = PP.getCurrentLexer())
        // The only lexer of the preprocessor is the compiler's `Lexer`. The text of a `_Pragma` has one of its own.
        Words = wordsFrom(static_cast<Lexer *>(Current)->getSourceLocation(), Start::Text, First);
      // A `#pragma` is reported at its first word, and the others where the compiler read them.
      const SourceLocation At = SM.getExpansionLoc(Kind == PIK_HashPragma && First.isValid() ? First : Loc);
      // A `#pragma` reads its name with no macro expansion, so `#pragma once` is the real one. The words of a `__pragma` are expanded first.
      if (At.isInvalid() || SM.isInSystemHeader(At) || (Kind == PIK_HashPragma && !Words.empty() && Words[0] == "once"))
        return;
      std::string Sentence;
      if (Words.size() == 2 && (Words[0] == "clang" || Words[0] == "GCC") && Words[1] == "diagnostic") {
        Sentence = "pragma diagnostic: not allowed in verified code. It silences the gate.";
        DiagnosticSeen = true;
      }
      else if (Words.size() == 2 && Words[1] == "system_header")
        Sentence = "pragma system_header: not allowed in verified code. It silences the gate.";
      else
        Sentence = std::string("pragma") + (Words.empty() ? "" : " " + Words[0] + (Words.size() > 1 ? " " + Words[1] : "")) +
                   ": not allowed in verified code. It changes the build the proofs assume.";
      report(At, Sentence);
    }
  };
};

// ------------------------------------------------------------ markers, decisions 0039 and 0047

// The reason of a marker is its first argument, a string literal with something in it. Empty when it has none.
std::string reasonOf(const AnnotateAttr *Note) {
  if (Note->args_size() == 0)
    return "";
  const auto *Text = dyn_cast<StringLiteral>((*Note->args_begin())->IgnoreImplicit()->IgnoreParens());
  return Text && Text->getCharByteWidth() == 1 ? Text->getString().trim().str() : "";
}

bool hasReason(const AnnotateAttr *Note) { return !reasonOf(Note).empty(); }

// A reason is one line, decision 0103: it holds no byte below 0x20, so it cannot put a line of its own into the report.
bool oneLine(const AnnotateAttr *Note) {
  const std::string Reason = reasonOf(Note);
  return std::none_of(Reason.begin(), Reason.end(), [](unsigned char C) { return C < 0x20; });
}

// The trusted marker of a function, decisions 0102 and 0103: its reason, and the declaration that wrote it. Nothing when the function is
// not trusted. The reason is empty when the marker has none that can be read, which the markers check refuses.
struct TrustedMark {
  std::string Reason;
  const FunctionDecl *At = nullptr;
};
std::optional<TrustedMark> trustedReason(const FunctionDecl *Function) {
  if (declaredKind(Function) != MarkerKind::Trusted)
    return std::nullopt;
  TrustedMark Mark;
  for (const FunctionDecl *D : declarationsOf(patternOf(Function)))
    forEachMarker(D, [&](const AnnotateAttr *Note) {
      if (markerKind(Note->getAnnotation()) != MarkerKind::Trusted || (Mark.At && !Mark.Reason.empty()))
        return;
      if (!Mark.At || !reasonOf(Note).empty())
        Mark = {reasonOf(Note), D};
    });
  return Mark;
}

// The reader of the markers. It walks the tree of one translation unit, outside the system headers, and reports in two forms under the
// name `cplusp-markers`. A third form, `reach {name}`, comes from the table of the lowered form, see `MarkersCheck`. A fourth,
// `uses {name}`, comes from `PlainUses`.
//  1. A region: the body of a function the file writes, or a plain declaration: a plain function, a plain class, a member of a plain
//     class that is written outside it, and the definition of its static data member. The diagnostic sits on the first byte of the region, so
//     the gate has that offset from clang-tidy as it has the offset of every finding. The message is
//     `region {verified|trusted|plain} {end offset}`, with no tab. The end offset is the offset of the byte after the last token. Both
//     offsets are those of the file place of the token. The region is no finding, and the gate keeps it and shows it to no bot.
//     Every function the file writes has one: a function, a member of a local class, an explicit specialization, and a lambda's body.
//     An instantiation and an implicit function have none. The core's `kind_at` picks the innermost region of a place.
//  2. A finding of the gate's own, with the exact words of the test: `{presumed file}\t{presumed line}\t{sentence}`, as the pragma check
//     reports. The sentence starts with `marker: `, and the gate maps it to the rule `marker`.
// A function takes the kind of the markers written on its own declarations. A marker with no reason is still honoured and still
// refused. Two kinds make the function verified. A trusted function has its body for its region, from the first written initializer or
// the brace. A plain function has every declaration, from its first token, which is the marker or the `template`, to its last.
// A trusted or plain function whose first or last token is in a macro is refused and has no region, so its body is verified. A function
// of any kind whose first and last token are in two files is refused and has no region, a lambda too. Code in a plain body is plain:
// a lambda, a local class and its members have no region of their own, and the region of the plain function covers them.
// ponytail: two ceilings. The semicolon after a declaration is not in its region. A plain method of a class template with a base that
// depends on the parameter is checked for its override at no instantiation, because the walk reads the pattern only. A virtual call
// that can run it is a call of the plain method, which the table of the lowered form reports.
// Upgrade: a visit of the instantiations for the override.
class MarkerReader : public RecursiveASTVisitor<MarkerReader> {
public:
  MarkerReader(ClangTidyCheck &Check, ASTContext &Context) : Check(Check), Context(Context), SM(Context.getSourceManager()) {}

  void read() { TraverseAST(Context); }

  bool TraverseDecl(Decl *D) {
    if (D && !isa<TranslationUnitDecl>(D) && isSystem(D->getLocation()))
      return true;
    return RecursiveASTVisitor<MarkerReader>::TraverseDecl(D);
  }

  // A declaration that is no function and no class takes no marker. A class takes a plain marker, decision 0051.
  bool VisitDecl(Decl *D) {
    if (D->isImplicit() || isa<FunctionDecl, FunctionTemplateDecl>(D))
      return true;
    forEachMarker(D, [&](const AnnotateAttr *Note) {
      const MarkerKind Named = markerKind(Note->getAnnotation());
      if (Named == MarkerKind::None)
        reportNoMarker(D, Note);
      else if (const auto *Class = dyn_cast<CXXRecordDecl>(D); Class && Named == MarkerKind::Plain)
        reportNoReason(Class, Note);
      else
        report(D, describe(D) + " has a marker, and only a function or a plain type takes one.");
    });
    return true;
  }

  // A plain class is plain from its first token to its last, with what it holds. A class nested in a plain class or defined in a plain
  // function has the region of that, and so has a member defined in the class. A class defined outside the plain class that holds it
  // gets a region of its own.
  bool VisitCXXRecordDecl(CXXRecordDecl *R) {
    if (!R->isThisDeclarationADefinition() || R->isImplicit() || R->isLambda() || !insidePlain(R) || coveredByPlain(R))
      return true;
    SourceLocation First = R->getBeginLoc();
    if (const ClassTemplateDecl *Template = R->getDescribedClassTemplate())
      First = Template->getBeginLoc();
    else if (const auto *Partial = dyn_cast<ClassTemplatePartialSpecializationDecl>(R))
      First = earlier(First, Partial->getTemplateParameters()->getTemplateLoc());
    SourceLocation Begin = First;
    for (const Attr *A : R->attrs())
      if (!A->isInherited() && !A->isImplicit())
        Begin = earlier(Begin, A->getRange().getBegin());
    place(R, MarkerKind::Plain, {First, R->getEndLoc()}, Begin);
    return true;
  }

  // The definition of a static data member outside its plain class is plain code too, `int Record::made = 0;`.
  bool VisitVarDecl(VarDecl *V) {
    if (V->isStaticDataMember() && V->isThisDeclarationADefinition() && !V->isImplicit() && insidePlain(V) && !coveredByPlain(V))
      place(V, MarkerKind::Plain, {V->getOuterLocStart(), V->getEndLoc()}, V->getOuterLocStart());
    return true;
  }

  bool VisitFunctionDecl(FunctionDecl *F) {
    // The compiler writes an implicit function, and an instantiation has the region of its pattern, which the walk meets too.
    if (F->isImplicit() || F->isTemplateInstantiation())
      return true;
    const MarkerKind Kind = kindOf(F);
    // Code in a plain body is plain, and the region of the plain function or class covers it, decisions 0048 and 0051.
    if (coveredByPlain(F))
      return true;
    // A plain function has a region over every declaration. So has a member of a plain class that is written outside it.
    if (insidePlain(F)) {
      place(F, MarkerKind::Plain, {firstTokenOf(F), F->getEndLoc()}, firstMarkerOf(F));
      return true;
    }
    // A function written in a plain class or function that is not plain itself keeps its declaration in view, decision 0052: a member
    // with a marker of its own, and a friend that the class defines. Its declaration is verified, and a trusted body sits on top of that.
    // A friend declaration has no code of its own, so it stays plain.
    if (insidePlain(outerOf(F, true)) && (F->getFriendObjectKind() == Decl::FOK_None || F->doesThisDeclarationHaveABody()))
      place(F, MarkerKind::Verified, {firstTokenOf(F), F->getEndLoc()}, firstMarkerOf(F));
    if (F->doesThisDeclarationHaveABody()) {
      const SourceRange Body = bodyRange(F);
      place(F, Kind == MarkerKind::Trusted ? Kind : MarkerKind::Verified, Body, Body.getBegin());
    }
    return true;
  }

  // A lambda is a function of its own with no marker, so it is verified inside a verified or a trusted body, and plain inside a plain
  // one. Its body is its region.
  bool VisitLambdaExpr(LambdaExpr *E) {
    const SourceRange Body = E->getBody()->getSourceRange();
    if (insidePlain(E->getLambdaClass()))
      return true;
    if (!keepsEnds(false, Body))
      reportAt(Check, SM, startOf(E->getBeginLoc()), "marker: this lambda " + std::string(EndsInTwoFiles));
    else
      addRegion(Body, MarkerKind::Verified);
    return true;
  }

private:
  ClangTidyCheck &Check;
  ASTContext &Context;
  const SourceManager &SM;
  std::map<const FunctionDecl *, MarkerKind> Kinds;  // by first declaration, so that each function is read and refused once

  bool isSystem(SourceLocation Loc) const { return Loc.isValid() && SM.isInSystemHeader(SM.getExpansionLoc(Loc)); }
  // Where a token starts in its file, and the place after it. A token from a macro stands at the call of the macro.
  SourceLocation startOf(SourceLocation Loc) const { return Loc.isValid() ? SM.getExpansionRange(Loc).getBegin() : Loc; }
  SourceLocation afterEndOf(SourceLocation Loc) const {
    return Loc.isValid() ? Lexer::getLocForEndOfToken(SM.getExpansionRange(Loc).getEnd(), 0, SM, Context.getLangOpts()) : Loc;
  }
  SourceLocation earlier(SourceLocation A, SourceLocation B) const {
    return B.isValid() && (A.isInvalid() || SM.isBeforeInTranslationUnit(B, A)) ? B : A;
  }

  static std::string describe(const Decl *D) {
    const auto *Named = dyn_cast<NamedDecl>(D);
    return Named && !Named->getName().empty() ? Named->getNameAsString() : "this declaration";
  }
  void report(const Decl *At, const std::string &Sentence) { reportAt(Check, SM, startOf(At->getLocation()), "marker: " + Sentence); }
  void reportNoReason(const NamedDecl *At, const AnnotateAttr *Note) {
    if (!hasReason(Note))
      report(At, At->getQualifiedNameAsString() + " has a marker with no reason. A trusted or plain marker gives its reason.");
  }
  void reportNoMarker(const Decl *At, const AnnotateAttr *Note) {
    const std::string Word = Note->getAnnotation().str();
    report(At, Word == "cplusp:assume" ? Word + " waits until a case needs it. Mark the function trusted with a reason."
                                       : Word + " is no marker. The markers are in include/cplusp.h.");
  }

  // The kind of a function. The first read refuses what is wrong with its markers, on every declaration in a user file.
  MarkerKind kindOf(const FunctionDecl *Function) {
    const auto Known = Kinds.find(Function->getFirstDecl());
    if (Known != Kinds.end())
      return Known->second;
    const std::string Name = Function->getQualifiedNameAsString();
    MarkerKind First = MarkerKind::None;
    const FunctionDecl *Brings = nullptr;  // the declaration with the first marker
    bool Twice = false;
    for (const FunctionDecl *D : declarationsOf(Function)) {
      if (isSystem(D->getLocation()))
        continue;
      forEachMarker(D, [&](const AnnotateAttr *Note) {
        const MarkerKind Named = markerKind(Note->getAnnotation());
        if (Named == MarkerKind::None)
          return reportNoMarker(D, Note);
        if (Named != MarkerKind::Verified && !hasReason(Note))
          report(D, Name + " has a marker with no reason. A trusted or plain marker gives its reason.");
        else if (Named != MarkerKind::Verified && !oneLine(Note))
          report(D, Name + " has a reason with a line break. A reason is one line.");
        if (First == MarkerKind::None) {
          First = Named;
          Brings = D;
        } else if (First != Named && !Twice) {
          Twice = true;
          report(D, Name + " has two kinds of marker. A function has one kind.");
        }
      });
    }
    const MarkerKind Kind = declaredKind(Function);
    if (Kind == MarkerKind::Trusted && Brings && !contractOf(SM, Function).Any)
      report(Brings, Name + " is trusted and has no contract. Its callers rest on the contract alone.");
    // A call of the base can run the override. A verified function may call the base, so the override must be as good as the base. A
    // member of a plain class is plain whether or not a marker says it, decision 0052. A marker brings the report to its declaration.
    if (const auto *Method = dyn_cast<CXXMethodDecl>(Function); Method && insidePlain(Function))
      for (const CXXMethodDecl *Base : cast<CXXMethodDecl>(Method->getCanonicalDecl())->overridden_methods())
        if (!insidePlain(Base)) {
          const std::string Over = Base->getQualifiedNameAsString();
          report(Brings ? Brings : Function, Method->getQualifiedNameAsString() + " is plain and overrides " + Over +
                                                  ", which is not plain. A verified call of " + Over + " can run it.");
        }
    return Kinds[Function->getFirstDecl()] = Kind;
  }

  // A body: the written constructor initializers, which the compiler sorts by member, and the block, as written. A macro stays a macro.
  SourceRange bodyRange(const FunctionDecl *F) const {
    const Stmt *Body = F->getBody();
    SourceLocation First = Body->getBeginLoc();
    if (const auto *Constructor = dyn_cast<CXXConstructorDecl>(F))
      for (const CXXCtorInitializer *Init : Constructor->inits())
        if (Init->isWritten())
          First = earlier(First, Init->getSourceRange().getBegin());
    return {First, Body->getEndLoc()};
  }

  static constexpr const char *EndsInTwoFiles =
      "starts or ends in a macro or in another file. Write its first and last token in its own file.";

  // Whether the first and last token of a function, as written, are in one file. A marked function keeps them outside a macro too.
  bool keepsEnds(bool Marked, SourceRange Edges) const {
    const SourceLocation First = Edges.getBegin(), Last = Edges.getEnd();
    if (First.isInvalid() || Last.isInvalid() || (Marked && (First.isMacroID() || Last.isMacroID())))
      return false;
    return SM.isWrittenInSameFile(startOf(First), startOf(Last));
  }

  // Where a function starts, with the markers before it. The marker before the first token is a macro itself.
  SourceLocation firstMarkerOf(const FunctionDecl *F) const {
    SourceLocation Begin = firstTokenOf(F);
    for (const Attr *A : F->attrs())
      if (!A->isInherited() && !A->isImplicit())
        Begin = earlier(Begin, A->getRange().getBegin());
    return Begin;
  }

  // The region of a function. `Edges` are its first and last token as written, and `Begin` is where the region starts, which is earlier
  // than the first token when a marker comes before it. The marker before the first token is a macro itself, and it is no edge. A function
  // that does not keep its ends has no region and is refused, whatever its kind, decisions 0047 and 0048.
  void place(const NamedDecl *F, MarkerKind Kind, SourceRange Edges, SourceLocation Begin) {
    if (!keepsEnds(Kind != MarkerKind::Verified, Edges)) {
      report(F, F->getQualifiedNameAsString() + " " + EndsInTwoFiles);
      return;
    }
    addRegion({Begin, Edges.getEnd()}, Kind);
  }

  void addRegion(SourceRange Range, MarkerKind Kind) {
    const SourceLocation Begin = startOf(Range.getBegin()), After = afterEndOf(Range.getEnd());
    if (Begin.isInvalid() || After.isInvalid() || !SM.isWrittenInSameFile(Begin, After) || SM.getFileOffset(After) <= SM.getFileOffset(Begin))
      return;
    const char *Word = Kind == MarkerKind::Trusted ? "trusted" : Kind == MarkerKind::Plain ? "plain" : "verified";
    Check.diag(Begin, "region %0 %1") << Word << StringRef(std::to_string(SM.getFileOffset(After)));
  }
};

// Whether a declaration is the library's: a system header declares it. A type of the library holds what its type arguments hold, and the
// library reads what it holds. The place decides, as for `inLibrary`, but the namespace does not: `__gnu_cxx` is the library too.
bool inSystemHeader(const Decl *D) {
  const SourceManager &SM = D->getASTContext().getSourceManager();
  return D->getLocation().isInvalid() || SM.isInSystemHeader(SM.getExpansionLoc(D->getLocation()));
}

const CXXRecordDecl *plainHeld(QualType Type);

// The plain class that a type argument of the library holds, or null. A pack holds what its elements hold.
const CXXRecordDecl *plainInArguments(ArrayRef<TemplateArgument> Args) {
  for (const TemplateArgument &A : Args)
    if (const CXXRecordDecl *Class = A.getKind() == TemplateArgument::Type   ? plainHeld(A.getAsType())
                                     : A.getKind() == TemplateArgument::Pack ? plainInArguments(A.pack_elements())
                                                                             : nullptr)
      return Class;
  return nullptr;
}

// The plain class that a value of a type is or holds, or null, decisions 0051 and 0052. An array holds its elements. A reference and a
// pointer hold nothing. A type of the library holds what its type arguments and the type around it hold, as the walk of decision 0046
// goes, so `std::vector<Record>` holds a `Record`. A type of the file that is not plain holds nothing here, because its own fields say.
const CXXRecordDecl *plainHeld(QualType Type) {
  const CXXRecordDecl *Class = Type.isNull() ? nullptr : Type->getBaseElementTypeUnsafe()->getAsCXXRecordDecl();
  if (!Class)
    return nullptr;
  if (insidePlain(Class))
    return Class;
  if (!inSystemHeader(Class))
    return nullptr;
  if (const auto *Spec = dyn_cast<ClassTemplateSpecializationDecl>(Class))
    if (const CXXRecordDecl *Held = plainInArguments(Spec->getTemplateArgs().asArray()))
      return Held;
  if (const auto *Outer = dyn_cast<CXXRecordDecl>(Class->getDeclContext()))
    return plainHeld(Class->getASTContext().getRecordType(Outer));
  return nullptr;
}

// The class that holds a member, and for a member of an anonymous union the class around it that has a name.
const CXXRecordDecl *plainOwner(const NamedDecl *Member) {
  const auto *Class = dyn_cast<CXXRecordDecl>(Member->getDeclContext());
  while (Class && Class->getDeclName().isEmpty() && isa<CXXRecordDecl>(Class->getDeclContext()))
    Class = cast<CXXRecordDecl>(Class->getDeclContext());
  return Class && insidePlain(Class) ? Class : nullptr;
}

// The uses of a plain type, decisions 0051 to 0054. Verified code makes no object of one: a variable, a field, a temporary, a `new` or a
// base. The same holds for a type of the library that holds one. It reads no field and no static data member of one, also in code that the
// compiler writes, as a structured binding does. It hands a plain object, or a pointer to one, only to a function that the file writes,
// because the library can read or copy what it gets. It casts such a pointer to no other type, because after the cast no callee can be
// judged. A reference and a pointer of the same type are allowed, and so is a call of a member that the file writes, which the reach rule
// judges. The reader reports `uses {class}` at each of these, wherever it is, and the gate keeps the ones in a verified place. A
// template is read at each instantiation too, and the place of an instantiation is the place of its pattern.
// ponytail: one ceiling. A use in an unevaluated operand, as in `sizeof(Record())`, is reported as well. Upgrade: a check of the types and
// the calls that the lowered form makes.
class PlainUses : public RecursiveASTVisitor<PlainUses> {
public:
  PlainUses(ClangTidyCheck &Check, ASTContext &Context) : Check(Check), Context(Context), SM(Context.getSourceManager()) {}

  void read() { TraverseAST(Context); }
  bool shouldVisitTemplateInstantiations() const { return true; }
  bool shouldVisitImplicitCode() const { return true; }

  bool TraverseDecl(Decl *D) {
    if (D && !isa<TranslationUnitDecl>(D) && D->getLocation().isValid() && SM.isInSystemHeader(SM.getExpansionLoc(D->getLocation())))
      return true;
    return RecursiveASTVisitor<PlainUses>::TraverseDecl(D);
  }

  bool VisitVarDecl(VarDecl *V) { return byValue(V->getType(), V->getLocation()); }
  bool VisitFieldDecl(FieldDecl *F) { return byValue(F->getType(), F->getLocation()); }
  bool VisitCXXNewExpr(CXXNewExpr *E) { return byValue(E->getAllocatedType(), E->getBeginLoc()); }
  // A temporary is an expression that is a value of the type. This holds a call that returns the type, a conversion and a copy.
  bool VisitExpr(Expr *E) { return E->isPRValue() ? byValue(E->getType(), E->getBeginLoc()) : true; }
  bool VisitCXXRecordDecl(CXXRecordDecl *R) {
    if (R->hasDefinition() && R->isThisDeclarationADefinition())
      for (const CXXBaseSpecifier &Base : R->bases())
        byValue(Base.getType(), Base.getBaseTypeLoc());
    return true;
  }
  bool VisitMemberExpr(MemberExpr *E) { return member(E->getMemberDecl(), E->getMemberLoc()); }
  bool VisitDeclRefExpr(DeclRefExpr *E) { return member(E->getDecl(), E->getLocation()); }
  // A call, also of a member or an operator, and a construction. The object of a member call is an argument too.
  bool VisitCallExpr(CallExpr *E) {
    if (const auto *Member = dyn_cast<CXXMemberCallExpr>(E))
      given(E->getDirectCallee(), Member->getImplicitObjectArgument());
    for (const Expr *Argument : E->arguments())
      given(E->getDirectCallee(), Argument);
    return true;
  }
  // A cast of a pointer to a plain object into a pointer of another type, written or made by the compiler, decision 0054. A `const void*`
  // keeps no type, so after the cast no callee can be judged on what it gets. A conversion to a base of the class counts too.
  bool VisitCastExpr(CastExpr *E) {
    const QualType From = E->getSubExpr()->getType();
    if (From->isPointerType() && E->getType()->isPointerType())
      if (const CXXRecordDecl *Class = plainPointee(From); Class && !sameClass(Class, plainPointee(E->getType())))
        use(Class, E->getBeginLoc());
    return true;
  }
  bool VisitCXXConstructExpr(CXXConstructExpr *E) {
    for (const Expr *Argument : E->arguments())
      given(E->getConstructor(), Argument);
    return true;
  }

private:
  ClangTidyCheck &Check;
  ASTContext &Context;
  const SourceManager &SM;
  std::set<std::pair<SourceLocation::UIntTy, const CXXRecordDecl *>> Seen;

  bool byValue(QualType Type, SourceLocation At) {
    use(plainHeld(Type), At);
    return true;
  }
  // A field, or a static data member.
  bool member(const ValueDecl *Member, SourceLocation At) {
    if (isa<FieldDecl>(Member) || (isa<VarDecl>(Member) && cast<VarDecl>(Member)->isStaticDataMember()))
      use(plainOwner(Member), At);
    return true;
  }
  // A plain object, by value or by reference, or a pointer to one, goes to a callee that the file does not write, decision 0053. A callee
  // with no name, as a pointer to a function is, may be the library's, so it counts. A function the file writes is judged by its own
  // kind, and the reach rule judges the call. A pointer counts as its object, because a C call such as `std::fwrite` takes an object so.
  // A pointer that is cast to another type is a use at the cast, `VisitCastExpr`.
  void given(const FunctionDecl *Callee, const Expr *Argument) {
    if (!Argument || (Callee && !inSystemHeader(Callee)))
      return;
    const CXXRecordDecl *Class = plainPointee(Argument->getType());
    use(Class ? Class : plainPointee(Argument->IgnoreParenImpCasts()->getType()), Argument->getBeginLoc());
  }
  static bool sameClass(const CXXRecordDecl *A, const CXXRecordDecl *B) { return B && A->getCanonicalDecl() == B->getCanonicalDecl(); }
  static const CXXRecordDecl *plainPointee(QualType Type) {
    while (!Type.isNull() && Type->isPointerType())
      Type = Type->getPointeeType();
    return plainHeld(Type);
  }
  void use(const CXXRecordDecl *Class, SourceLocation At) {
    if (!Class || At.isInvalid() || SM.isInSystemHeader(SM.getExpansionLoc(At)))
      return;
    At = SM.getExpansionLoc(At);
    if (Seen.insert({At.getRawEncoding(), Class->getCanonicalDecl()}).second)
      Check.diag(At, "uses %0") << StringRef(Class->getQualifiedNameAsString());
  }
};

// cplusp-markers: decisions 0039 and 0047. The plugin reads the markers of include/cplusp.h. See `MarkerReader` for what it reports.
// It reports the calls that run plain code too, from the table of the lowered form, as `reach {qualified name}` at the call. The name
// runs to the end of the message and may hold a space. The gate keeps such a report when the place of the call is verified. Every
// function that the file wrote reports its calls, whatever its kind, because the kind of the place is the gate's to ask.
// A file that the compiler cannot generate code for is refused, because the gate then cannot read what runs.
class MarkersCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void onStartOfTranslationUnit() override { startTable(); }
  void registerMatchers(MatchFinder *Finder) override {
    registerTableMatchers(Finder, this);
    Finder->addMatcher(translationUnitDecl(), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    giveTable(Result.Context);
    if (collectForTable(Result))
      return;
    Context = Result.Context;
    MarkerReader(*this, *Result.Context).read();
    PlainUses(*this, *Result.Context).read();
  }
  void onEndOfTranslationUnit() override {
    Lowered &T = table();
    if (!Context)
      return;
    if (!T.generated()) {
      const SourceManager &SM = Context->getSourceManager();
      reportAt(*this, SM, SM.getLocForStartOfFile(SM.getMainFileID()),
               "marker: the compiler could not generate code for this file, so the gate cannot read what runs.");
    }
    for (const Lowered::PlainCall &Call : T.plainCalls())
      diag(Call.Loc, "reach %0") << StringRef(Call.Name);
  }

private:
  ASTContext *Context = nullptr;
};

// cplusp-indirect-call: decision 0048. The row `function_pointers` judges a call too, not only the spelling of a type. Verified code can
// run an indirect call, itself or through code that the file does not write, and a deduced type carries a pointer out of a trusted body
// with none spelled. When the lowered form cannot name each target, the call is a finding of the row, at its line. The gate writes the
// message of the row, so the text here only has to map. The row is trusted only, so the core drops the finding in a trusted or plain place.
class IndirectCallCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void onStartOfTranslationUnit() override { startTable(); }
  void registerMatchers(MatchFinder *Finder) override {
    registerTableMatchers(Finder, this);
    Finder->addMatcher(translationUnitDecl(), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    giveTable(Result.Context);
    if (collectForTable(Result))
      return;
    Seen = true;
  }
  void onEndOfTranslationUnit() override {
    if (!Seen)
      return;
    for (const SourceLocation &At : table().indirectCalls())
      diag(At, "an indirect call that the gate cannot name the target of");
  }

private:
  bool Seen = false;
};

// cplusp-tree: decisions 0056 and 0057. The plugin writes the tree of each function the file defines as data, and the core decides
// what it means. One JSON object on one line, appended to the file of the option `Output`, in the shape of the core's types, with names
// as strings. The shell numbers them. This check decides nothing. It keeps every implicit node, and it looks through no cast and no
// parenthesis. A node it has no name for is `{"Unknown": [class, line]}`, and the core refuses it.
// ponytail: a qualified type, a `const int` for one, is `Other`, so the translator refuses it. The slice has no const yet.
// Upgrade: drop the qualifiers that keep the value, once the core has a rule for them.
class TreeWriter {
public:
  // `Claimed` takes the `//@` lines that a loop owns, so the orphan scan skips them.
  // `Structs` takes each plain struct that a type names, by its key, so the check writes it once.
  TreeWriter(ASTContext &Context, std::set<std::pair<unsigned, unsigned>> &Claimed, std::map<std::string, llvm::json::Value> &Structs)
      : Context(Context), SM(Context.getSourceManager()), Mangler(Context.createMangleContext()), Claimed(Claimed), Structs(Structs) {}

  // The key of a function, decision 0058: its Itanium mangled name. The name tells overloads and namespaces apart, and it is the same
  // for a call and for the definition. A function with no mangled name, or one that is templated, a constructor or a destructor, has
  // its qualified name as printed for diagnostics, then `@` and the place of its definition, or of its canonical declaration when it
  // has none. A mangled name has no `@`, so the two kinds never clash.
  std::string key(const FunctionDecl *FD) const {
    if (!FD->isTemplated() && !FD->isDependentContext() && !isa<CXXConstructorDecl>(FD) && !isa<CXXDestructorDecl>(FD) &&
        Mangler->shouldMangleDeclName(FD)) {
      std::string Out;
      llvm::raw_string_ostream OS(Out);
      Mangler->mangleName(GlobalDecl(FD), OS);
      return Out;
    }
    const FunctionDecl *At = FD->getDefinition() ? FD->getDefinition() : FD->getCanonicalDecl();
    const SourceLocation Loc = SM.getFileLoc(At->getLocation());
    return name(FD) + "@" + file(Loc) + ":" + std::to_string(line(Loc)) + ":" + std::to_string(SM.getExpansionColumnNumber(Loc));
  }
  std::string name(const FunctionDecl *FD) const {
    std::string Out;
    llvm::raw_string_ostream OS(Out);
    FD->getNameForDiagnostic(OS, Context.getPrintingPolicy(), true);
    return Out;
  }

  // ponytail: a function the translator cannot read, a template, a member or one with no body, is written with no signature and no
  // contract, only a body of one `Unknown`. Its return type is `Other` with the opaque kind, so the core refuses its signature by that
  // kind, and a caller sees a callee with no method. Its contract lines still count as claimed.
  // Upgrade: a core rule for these, and their real signature.
  llvm::json::Value function(const FunctionDecl *FD, const Contract &C) const {
    // A trusted function is written with its contract and no body, whatever body it has, decision 0102. `trusted` holds its reason.
    // It is the reason, the file and the line of the declaration with the marker, for the report of prove.
    const std::optional<TrustedMark> Trusted = trustedReason(FD);
    const llvm::json::Value TrustedJson =
        Trusted ? llvm::json::Value(llvm::json::Array{Trusted->Reason, file(Trusted->At->getLocation()), number(line(Trusted->At->getLocation()))})
                : llvm::json::Value(nullptr);
    const CXXMethodDecl *Member = member(FD);
    // A static member function is a free function with the name of its class, `Tally::bump`, and no `this`, decision 0174.
    // One with no contract stays refused as `CXXMethodDecl`, as the tests of decision 0089 pin.
    const CXXMethodDecl *Static = listedStatic(FD) ? cast<CXXMethodDecl>(FD) : nullptr;
    // An interface method is written at its declaration only. A pure virtual function that has a body is none: the body has no rule, decision 0165.
    const bool PureBody = ifaceMethod(FD) && FD->isThisDeclarationADefinition();
    // A const pure virtual function that gives no value has no rule yet, decision 0166. One that writes its object gives its object back, decision 0169.
    const bool NoValue = ifaceMethod(FD) && !PureBody && FD->getReturnType()->isVoidType() && cast<CXXMethodDecl>(FD)->isConst();
    const bool Interface = ifaceMethod(FD) && !PureBody && !NoValue;
    const CXXConstructorDecl *Constructor = valueConstructor(FD);
    const char *Opaque = PureBody                                  ? "a body of a pure virtual function"
                         : NoValue                                   ? "a pure virtual function that gives no value"
                         : FD->isTemplated()                         ? "FunctionTemplateDecl"
                         : !Constructor && noDestructorMove(FD)       ? "a move constructor in a struct with no destructor"
                         : isa<CXXConstructorDecl>(FD) && !Constructor ? "CXXConstructorDecl"
                         : isa<CXXMethodDecl>(FD) && !Member && !Static && !Constructor ? "CXXMethodDecl"
                         : !FD->getBody() && !Trusted && !Interface ? "FunctionDecl without body"
                                                  : nullptr;
    llvm::json::Array Params, Conds;
    Enclosing = FD;
    llvm::json::Value Hidden = hiddenConstants(FD);
    if (!Opaque) {
      // A member function takes its object as a parameter `this` by value, first, decision 0089. Its contract lines name it first too.
      // One that is not const writes its object and gives it back, decision 0096.
      if (Member)
        Params.push_back(llvm::json::Array{"this", thisType(Member->getParent(), !Member->isConst())});
      // ponytail: a trusted function that takes `const S&` has the parameter as a value in the model. Decision 0103 promises that its body
      // changes no such parameter, and the gate does not check it: a `const_cast` in a trusted body can break the promise. Upgrade: a gate
      // check of `const_cast` on a parameter or on `this` in a trusted body.
      for (const ParmVarDecl *P : FD->parameters())
        Params.push_back(llvm::json::Array{P->getNameAsString(), paramType(P->getType())});
      Conds = conds(C, Member != nullptr);
      // The `//@` lines in a trusted body belong to it, decision 0103. The walk claims them, and the result is dropped.
      if (Trusted && FD->getBody())
        (void)stmts(FD->getBody());
    }
    // A constructor gives the struct that it builds, decision 0094. Its result type is `This`, and its contract has no `this` parameter.
    if (Constructor)
      return llvm::json::Object{{"name", FD->getNameAsString()},
                                {"key", key(FD)},
                                {"file", file(FD->getLocation())},
                                {"line", number(line(FD->getLocation()))},
                                {"params", std::move(Params)},
                                {"ret", thisType(Constructor->getParent())},
                                {"trusted", TrustedJson},
                                {"hidden", std::move(Hidden)},
                                {"conds", std::move(Conds)},
                                {"body", Trusted ? llvm::json::Array{} : constructorBody(Constructor)}};
    // The destructor is the member `~`, decision 0178.
    llvm::json::Object Out{{"name", Static ? name(FD) : isa<CXXDestructorDecl>(FD) ? std::string("~") : FD->getNameAsString()},
                              {"key", key(FD)},
                              {"file", file(FD->getLocation())},
                              {"line", number(line(FD->getLocation()))},
                              {"params", std::move(Params)},
                              {"ret", Opaque ? tag("Other", Opaque) : FD->getReturnType()->isVoidType() ? llvm::json::Value("Void") : resultType(FD->getReturnType())},
                              {"trusted", TrustedJson},
                              {"interface", Interface},
                              {"hidden", std::move(Hidden)},
                              {"conds", std::move(Conds)},
                              {"body", Opaque ? llvm::json::Array{tag("Unknown", llvm::json::Array{Opaque, number(line(FD->getLocation()))})}
                                       : Trusted || Interface ? llvm::json::Array{}
                                                 : stmts(FD->getBody())}};
    // The class of a static member function, as the contract of the function reads a bare call, decision 0174.
    if (Static)
      Out["static"] = Static->getParent()->getQualifiedNameAsString();
    return Out;
  }

  std::string file(SourceLocation At) const { return SM.getFilename(SM.getFileLoc(At)).str(); }

  // A `constexpr` variable declared at the scope of the file, of any type, or null. A namespace is no scope of the file, nor is a class or a template.
  static const VarDecl *fileConstexpr(const ValueDecl *D) {
    const auto *Var = dyn_cast<VarDecl>(D);
    return Var && Var->isConstexpr() && Var->getDeclContext()->isTranslationUnit() && !isa<VarTemplateSpecializationDecl>(Var) && !Var->isTemplated() ? Var : nullptr;
  }
  // The value of a named constant, decision 0106: a `constexpr` variable of an integer type, declared at the scope of the file. Null when
  // the variable is none. A namespace is no scope of the file. A constant of a namespace or of a class can hide one of the file from a
  // function, so `function` writes the names that it hides, decision 0107.
  std::optional<llvm::APSInt> constant(const ValueDecl *D) const {
    const auto *Var = fileConstexpr(D);
    if (!Var)
      return std::nullopt;
    const QualType T = Var->getType().getCanonicalType().getUnqualifiedType();
    const char *S = scalar(T) ? scalar(T) : smallScalar(T);
    const APValue *Value = S && StringRef(S) != "Bool" ? Var->evaluateValue() : nullptr;
    if (!Value || !Value->isInt())
      return std::nullopt;
    return Value->getInt();
  }
  // The value of a named double constant, decision 0158: a `constexpr` variable of type double at the scope of the file, as `constant` takes an integer one.
  std::optional<double> realConstant(const ValueDecl *D) const {
    const auto *Var = fileConstexpr(D);
    if (!Var || !isDouble(Var->getType().getCanonicalType().getUnqualifiedType()))
      return std::nullopt;
    const APValue *Value = Var->evaluateValue();
    if (!Value || !Value->isFloat())
      return std::nullopt;
    return Value->getFloat().convertToDouble();
  }
  // Whether a scope declares a name, or a using-directive of the scope brings one in, decision 0107. A function holds its locals in its list of
  // declarations, not in its table of names, so its list is read. `Seen` stops a cycle of directives. The table of the translation unit holds the
  // constants of the file themselves, so `Own` is false for it: only its directives count.
  // ponytail: a function's locals, and the later declarations of a namespace, hide the name from the whole function. This refuses some correct
  // programs. Upgrade: look up from the point of the declaration.
  static bool declares(const DeclContext *DC, DeclarationName Name, std::set<const DeclContext *> &Seen, bool Own = true) {
    DC = DC->getPrimaryContext();
    if (!Seen.insert(DC).second)
      return false;
    if (isa<FunctionDecl>(DC)) {
      for (const Decl *D : DC->decls()) {
        if (const auto *Named = dyn_cast<NamedDecl>(D); Named && Named->getDeclName() == Name)
          return true;
      }
      // ponytail: a using-directive in a function body is not looked through. The gate bans it in verified and trusted code. Upgrade: find
      // each UsingDirectiveDecl in the DeclStmts of the body.
      return false;
    }
    if (Own && !DC->lookup(Name).empty())
      return true;
    for (const UsingDirectiveDecl *Using : DC->using_directives())
      if (Using->getNominatedNamespace() && declares(Using->getNominatedNamespace(), Name, Seen))
        return true;
    return false;
  }
  // The names of the constants of the file that C++ does not find from the function, decision 0107. Unqualified lookup goes out from the function
  // through its class, the bases of the class, the functions and namespaces around it, and the using-directives of each, to the file. A name that one
  // of them declares hides the constant of the file, and so does a directive of the file that brings in the same name: it has two meanings then.
  llvm::json::Array hiddenConstants(const FunctionDecl *FD) const {
    llvm::json::Array Out;
    for (const Decl *D : Context.getTranslationUnitDecl()->decls()) {
      const auto *Var = dyn_cast<VarDecl>(D);
      if (!Var || !Var->isConstexpr() || !(constant(Var) || realConstant(Var)))
        continue;
      const DeclarationName Name = Var->getDeclName();
      bool Hidden = false;
      for (const DeclContext *DC = FD->getDeclContext(); DC && !DC->isTranslationUnit() && !Hidden; DC = DC->getParent()) {
        std::set<const DeclContext *> Seen;
        Hidden = declares(DC, Name, Seen);
        if (const auto *RD = dyn_cast<CXXRecordDecl>(DC); RD && !Hidden && RD->hasDefinition())
          Hidden = !RD->forallBases([&](const CXXRecordDecl *Base) {
            std::set<const DeclContext *> BaseSeen;
            return !declares(Base, Name, BaseSeen);
          });
      }
      std::set<const DeclContext *> Seen;
      // An inline namespace puts its names in the table of its parent and makes no directive, so a second declaration of the name in the table of the
      // file is one of an inline namespace.
      const DeclContext::lookup_result AtFile = Context.getTranslationUnitDecl()->lookup(Name);
      if (Hidden || std::distance(AtFile.begin(), AtFile.end()) > 1 || declares(Context.getTranslationUnitDecl(), Name, Seen, false))
        Out.push_back(Var->getNameAsString());
    }
    // The words of a contract hide a name of C++, decision 0158. A word that C++ finds from the function as a name is listed, so a contract line that reads
    // the word is refused. C++ looks from the function through its parameters and locals, its class and the bases of the class, the namespaces around it
    // and the file. An out-of-line member is looked up in its class, because the semantic context is the class.
    for (const char *Word : {"eps", "eta", "DBL_MAX"}) {
      const DeclarationName Name = &Context.Idents.get(Word);
      std::set<const DeclContext *> Seen;
      bool Found = declares(FD, Name, Seen);
      // The semantic context, and the lexical one when it differs: the body of a friend that a class defines is looked up in the class.
      for (const DeclContext *Start : {FD->getDeclContext(), FD->getLexicalDeclContext()}) {
        for (const DeclContext *DC = Start; DC && !Found; DC = DC->getParent()) {
          std::set<const DeclContext *> Visited;
          Found = declares(DC, Name, Visited);
          if (const auto *RD = dyn_cast<CXXRecordDecl>(DC); RD && !Found && RD->hasDefinition())
            Found = !RD->forallBases([&](const CXXRecordDecl *Base) {
              std::set<const DeclContext *> BaseSeen;
              return !declares(Base, Name, BaseSeen);
            });
        }
      }
      if (Found)
        Out.push_back(Word);
    }
    return Out;
  }
  // Writes the item of an enum class of the file, so a contract can name its enumerators though no code names its type, decision 0114.
  void writeEnum(const EnumDecl *ED) const {
    if (plainEnum(Context.getTypeDeclType(ED)))
      enumType(ED);
    else if (valuedEnum(Context.getTypeDeclType(ED)))
      valuedType(ED);
  }
  // The line of the tree for a named constant, or null.
  llvm::json::Value constantLine(const VarDecl *Var) const {
    // A double constant has a line when its value is `m / q`, decision 0158: the sign, `m` and `q`.
    if (const std::optional<double> Real = realConstant(Var)) {
      uint64_t M, Q;
      if (!std::isfinite(*Real) || !dyadic(std::fabs(*Real), M, Q))
        return nullptr;
      return llvm::json::Object{{"constant", Var->getNameAsString()}, {"real", llvm::json::Array{std::signbit(*Real) && *Real != 0.0, number(M), number(Q)}}};
    }
    const std::optional<llvm::APSInt> Value = constant(Var);
    if (!Value)
      return nullptr;
    llvm::SmallString<32> Text;
    Value->toString(Text);
    return llvm::json::Object{{"constant", Var->getNameAsString()}, {"value", std::string(Text)}};
  }
  // The line of the tree for a mutable global or a static data member that the file defines, decision 0173: its name and its type. The shell
  // lists them in this order, which is the order of the definitions.
  llvm::json::Value globalLine(const VarDecl *Var) const {
    if (!isGlobal(Var) || !Var->isThisDeclarationADefinition())
      return nullptr;
    return llvm::json::Object{{"global", nameOf(Var)}, {"ty", type(Var->getType())}};
  }
  // A mutable global or static data member, not a function-local static and not a name of the standard library, decision 0173.
  static bool isGlobal(const ValueDecl *D) {
    const auto *Var = dyn_cast<VarDecl>(D);
    return Var && isMutableGlobal(Var) && !Var->isStaticLocal() && !Var->isInStdNamespace();
  }
  // The name of a variable in the tree. A static data member has its qualified name as one word, `Registry::last_id`, decision 0173.
  static std::string nameOf(const ValueDecl *D) {
    const auto *Var = dyn_cast<VarDecl>(D);
    return Var && Var->isStaticDataMember() ? Var->getQualifiedNameAsString() : D->getNameAsString();
  }

private:
  ASTContext &Context;
  const SourceManager &SM;
  std::unique_ptr<MangleContext> Mangler;
  std::set<std::pair<unsigned, unsigned>> &Claimed;
  std::map<std::string, llvm::json::Value> &Structs;
  mutable std::set<const CXXRecordDecl *> Visiting;  // the structs whose fields `plainStruct` is reading
  mutable bool InConstructorBody = false;  // `constructorBody` is writing the statements of a body, where a field and `this` have no rule, decision 0179
  mutable const FunctionDecl *Enclosing = nullptr;  // the function that `function` is writing, the floor of a loop's walk upward

  // The contract lines as data. A line of a loop has no parameters.
  llvm::json::Array conds(const Contract &C, bool Member = false) const {
    llvm::json::Array Out;
    for (const Contract::Line &L : C.Lines) {
      llvm::json::Array Names;
      if (Member)
        Names.push_back("this");
      for (const std::string &N : L.Params)
        Names.push_back(N);
      // The word ends at any white space.
      const StringRef Text = L.Text;
      const size_t Cut = Text.find_first_of(" \t\f\v\r");
      Out.push_back(llvm::json::Object{
          {"kind", Text.substr(0, Cut).str()}, {"file", file(SM.getLocForStartOfFile(L.Id))}, {"line", number(L.Number)}, {"text", Cut == StringRef::npos ? "" : Text.substr(Cut).trim().str()},
          {"params", std::move(Names)}});
    }
    return Out;
  }
  // The `//@` lines directly above a loop, claimed for it. They stop at the start of the body of the function, so a loop on the line of
  // its function leaves the function its lines.
  llvm::json::Array loopConds(const Stmt *Loop) const {
    Contract C = linesAbove(Loop);
    for (const Contract::Line &L : C.Lines)
      Claimed.insert({L.File, L.Number});
    // An assert or apply line above a loop is a statement before it, `bodyLines`. The loop keeps its invariant and decreases lines.
    C.Lines.erase(std::remove_if(C.Lines.begin(), C.Lines.end(), isBodyLine), C.Lines.end());
    return conds(C);
  }
  // The `//@` lines directly above a statement, up to the start of the body of the function.
  Contract linesAbove(const Stmt *S, bool SkipComments = false) const {
    const Stmt *Body = Enclosing ? Enclosing->getBody() : nullptr;
    return contractAbove(SM, S->getBeginLoc(), Body ? Body->getBeginLoc() : SourceLocation(), SkipComments);
  }
  // Whether only white space is before the statement on its line. A statement after code, as the `if` of `} else if`, takes no line above.
  bool startsItsLine(const Stmt *S) const {
    const SourceLocation At = SM.getExpansionLoc(S->getBeginLoc());
    if (At.isInvalid())
      return false;
    const auto [File, Offset] = SM.getDecomposedLoc(At);
    bool Invalid = false;
    const StringRef Text = SM.getBufferData(File, &Invalid);
    if (Invalid)
      return false;
    const size_t Newline = Text.substr(0, Offset).rfind('\n');
    return Text.slice(Newline == StringRef::npos ? 0 : Newline + 1, Offset).trim().empty();
  }
  static bool isBodyLine(const Contract::Line &L) {
    const StringRef Text = L.Text;
    const StringRef Word = Text.substr(0, Text.find_first_of(" \t\f\v\r"));
    return Word == "assert" || Word == "apply";
  }
  // The assert and apply lines directly above a statement, as statements of their own, decision 0099. A line that an outer statement on
  // the same line took first is not taken again.
  void bodyLines(const Stmt *S, llvm::json::Array &Out) const {
    if (!startsItsLine(S))
      return;
    Contract C = linesAbove(S, true);
    // A line that is no assert or apply line is dropped, and so is one that was taken already.
    C.Lines.erase(std::remove_if(C.Lines.begin(), C.Lines.end(), [&](const Contract::Line &L) { return !isBodyLine(L) || !Claimed.insert({L.File, L.Number}).second; }),
                  C.Lines.end());
    for (const Contract::Line &L : C.Lines) {
      Contract One;
      One.Lines.push_back(L);
      llvm::json::Value Cond = std::move(conds(One).front());
      Out.push_back(tag(StringRef(L.Text).starts_with("assert") ? "Assert" : "Apply", std::move(Cond)));
    }
  }

  static llvm::json::Value number(uint64_t N) { return llvm::json::Value(N); }
  unsigned line(SourceLocation At) const { return SM.getExpansionLineNumber(At); }
  static llvm::json::Value tag(const char *Name, llvm::json::Value Inner) { return llvm::json::Object{{Name, std::move(Inner)}}; }
  // A node with no valid place, a default argument, takes the line of the call or statement around it.
  llvm::json::Value unknown(const Stmt *S, const std::string &What, unsigned Near) const {
    return tag("Unknown", llvm::json::Array{What, number(S->getBeginLoc().isValid() ? line(S->getBeginLoc()) : Near)});
  }
  // What the bot reads for a node with no rule. An expression statement and the same expression inside another give the same words.
  static std::string describe(const Stmt *S) {
    // A statement that makes a temporary, such as `r = x;` on an optional, is wrapped for its cleanups. The wrapper is not the construct.
    if (const auto *Cleanups = dyn_cast<ExprWithCleanups>(S))
      return describe(Cleanups->getSubExpr());
    if (const auto *Binary = dyn_cast<BinaryOperator>(S))
      return std::string("BinaryOperator ") + Binary->getOpcodeStr().str();
    if (const auto *Unary = dyn_cast<UnaryOperator>(S))
      return std::string("UnaryOperator ") + UnaryOperator::getOpcodeStr(Unary->getOpcode()).str();
    return S->getStmtClassName();
  }

  // The scalar of the subset that a type is, as the core names it, or null. A qualified type is none.
  const char *scalar(QualType T) const {
    const QualType Canon = T.getCanonicalType();
    if (Canon.hasQualifiers())
      return nullptr;
    if (const auto *Builtin = dyn_cast<BuiltinType>(Canon.getTypePtr())) {
      const uint64_t Bits = Context.getTypeSize(Canon);
      switch (Builtin->getKind()) {
      case BuiltinType::Int:
        return Bits == 32 ? "I32" : nullptr;
      case BuiltinType::Long:
      case BuiltinType::LongLong:
        return Bits == 64 ? "I64" : nullptr;
      case BuiltinType::UChar:
        return "U8";
      case BuiltinType::UInt:
        return Bits == 32 ? "U32" : nullptr;
      case BuiltinType::ULong:
      case BuiltinType::ULongLong:
        return Bits == 64 ? "U64" : nullptr;
      case BuiltinType::Bool:
        return "Bool";
      default:
        return nullptr;
      }
    }
    return nullptr;
  }

  // The small integer types of decision 0106: `int8_t`, `int16_t` and `uint16_t`, or null. They are types of the subset, but no element of a
  // sequence and no value of an optional, so `scalar` does not name them. They can be a field, decision 0138.
  const char *smallScalar(QualType T) const {
    const QualType Canon = T.getCanonicalType();
    if (Canon.hasQualifiers())
      return nullptr;
    if (const auto *Builtin = dyn_cast<BuiltinType>(Canon.getTypePtr())) {
      const uint64_t Bits = Context.getTypeSize(Canon);
      switch (Builtin->getKind()) {
      case BuiltinType::SChar:
        return Bits == 8 ? "I8" : nullptr;
      case BuiltinType::Short:
        return Bits == 16 ? "I16" : nullptr;
      case BuiltinType::UShort:
        return Bits == 16 ? "U16" : nullptr;
      default:
        return nullptr;
      }
    }
    return nullptr;
  }

  // Whether a type is `double` with no qualifier, decision 0150. `float` and `long double` are refused by the gate.
  static bool isDouble(QualType T) {
    const QualType Canon = T.getCanonicalType();
    const auto *Builtin = dyn_cast<BuiltinType>(Canon.getTypePtr());
    return !Canon.hasQualifiers() && Builtin && Builtin->getKind() == BuiltinType::Double;
  }

  // The element type of a read-only sequence, decision 0064, or null: a const vector or a reference to one, except `std::vector<bool>`, and
  // a span of const elements, any extent, and a const std::array, decision 0132. A reference is looked through. The element is a scalar or a plain struct, decision 0076. A
  // `Field` is a field of a struct, decision 0076: a vector with no const, and no span.
  QualType seqElement(QualType T, bool Field = false) const {
    const bool Reference = T->isReferenceType();
    if (Reference)
      T = T->getPointeeType();
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(T->getAsCXXRecordDecl());
    if (!Spec || !Spec->isInStdNamespace() || Spec->getTemplateArgs().size() == 0 || Spec->getTemplateArgs()[0].getKind() != TemplateArgument::Type)
      return QualType();
    QualType Elem = Spec->getTemplateArgs()[0].getAsType();
    if (Spec->getName() == "vector") {
      if (!(Field || T.isConstQualified()) || Elem.getCanonicalType().hasQualifiers())
        return QualType();
      const char *S = scalar(Elem);
      // A unique_ptr of a struct or an interface is an element of a vector, not of a field, decision 0170.
      if (!Field && !ownVecElement(Elem).isNull())
        return Elem;
      return (S ? StringRef(S) != "Bool" : plainStruct(Elem) != nullptr) ? Elem : QualType();
    }
    if (!Field && Spec->getName() == "span" && Elem.isConstQualified()) {
      Elem.removeLocalConst();
      return scalar(Elem) || (!Elem.getCanonicalType().hasQualifiers() && plainStruct(Elem)) ? Elem : QualType();
    }
    // A const std::array of a scalar or a plain struct is a sequence of fixed length, decision 0132. The plugin passes an array of bool on, and the core
    // refuses it, decision 0136.
    // A std::array by value is a copy that only the function sees, so it is a read-only sequence too, decision 0175.
    if (!Field && Spec->getName() == "array" && (T.isConstQualified() || !Reference) && !T.isVolatileQualified() && !Elem.getCanonicalType().hasQualifiers())
      return scalar(Elem) || plainStruct(Elem) ? Elem : QualType();
    return QualType();
  }
  bool isSeq(QualType T) const { return !seqElement(T).isNull(); }

  // The fixed extent of a read-only sequence, decisions 0070 and 0132, or null: a vector, and a span of `std::dynamic_extent`. A std::array has its length.
  llvm::json::Value seqExtent(QualType T) const {
    if (T->isReferenceType())
      T = T->getPointeeType();
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(T->getAsCXXRecordDecl());
    if (!Spec || (Spec->getName() != "span" && Spec->getName() != "array") || Spec->getTemplateArgs().size() < 2 || Spec->getTemplateArgs()[1].getKind() != TemplateArgument::Integral)
      return nullptr;
    llvm::APSInt N = Spec->getTemplateArgs()[1].getAsIntegral();
    return N.isNegative() || N.getActiveBits() > 63 || N.isAllOnes() ? llvm::json::Value(nullptr) : llvm::json::Value(static_cast<int64_t>(N.getZExtValue()));
  }

  // The element of a `std::optional` of a scalar or of a plain struct, decisions 0075 and 0137, or null: by value, or by const lvalue
  // reference. A write handle, a volatile optional and an optional of anything else are none.
  QualType optType(QualType T) const {
    if (T->isReferenceType()) {
      if (!T->isLValueReferenceType() || !T->getPointeeType().isConstQualified())
        return QualType();
      T = T->getPointeeType();
    }
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(T->getAsCXXRecordDecl());
    if (T.isVolatileQualified() || !Spec || !Spec->isInStdNamespace() || Spec->getName() != "optional" || Spec->getTemplateArgs().size() != 1 ||
        Spec->getTemplateArgs()[0].getKind() != TemplateArgument::Type)
      return QualType();
    const QualType Elem = Spec->getTemplateArgs()[0].getAsType();
    // The element is a scalar, or a plain struct with no qualifier, decision 0137.
    return scalar(Elem) || (!Elem.getCanonicalType().hasQualifiers() && plainStruct(Elem)) ? Elem : QualType();
  }

  // The scalar of an optional of a scalar, or null. A field of a struct may hold such an optional, and no other.
  const char *optElement(QualType T) const {
    const QualType Elem = optType(T);
    return Elem.isNull() ? nullptr : scalar(Elem);
  }
  // Whether a type is an optional of a scalar or of a plain struct.
  bool isOpt(QualType T) const { return !optType(T).isNull(); }

  // The element of a `std::unique_ptr` that the code only reads, decision 0142, or null: `std::unique_ptr<T>` with the default deleter, for a
  // scalar or a plain struct with no qualifier. The type of a value or of a name that reads one, so no reference.
  QualType ownElement(QualType T) const {
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(T.getUnqualifiedType()->getAsCXXRecordDecl());
    if (T->isReferenceType() || T.isVolatileQualified() || !Spec || !Spec->isInStdNamespace() || Spec->getName() != "unique_ptr" ||
        Spec->getTemplateArgs().size() != 2 || Spec->getTemplateArgs()[0].getKind() != TemplateArgument::Type ||
        Spec->getTemplateArgs()[1].getKind() != TemplateArgument::Type)
      return QualType();
    const QualType Elem = Spec->getTemplateArgs()[0].getAsType();
    const CXXRecordDecl *Deleter = Spec->getTemplateArgs()[1].getAsType()->getAsCXXRecordDecl();
    if (!Deleter || !Deleter->isInStdNamespace() || Deleter->getName() != "default_delete")
      return QualType();
    // A scalar, a plain struct, or an interface, decision 0168.
    return !Elem.getCanonicalType().hasQualifiers() && (scalar(Elem) || plainStruct(Elem) || isInterface(Elem->getAsCXXRecordDecl())) ? Elem : QualType();
  }
  bool isOwn(QualType T) const { return !ownElement(T).isNull(); }
  // A `std::unique_ptr` of a struct or an interface with no qualifier, as the element of a vector, decision 0170, or null.
  QualType ownVecElement(QualType Elem) const {
    if (Elem.isNull() || Elem.getCanonicalType().hasQualifiers())
      return QualType();
    const QualType Pointee = ownElement(Elem);
    return !Pointee.isNull() && Pointee->getAsCXXRecordDecl() ? Elem : QualType();
  }
  // The type of an element of a sequence for the core. A unique_ptr is `Own` of its key, and any other element is its type, decision 0170.
  llvm::json::Value elementType(QualType Elem) const {
    if (const QualType Held = ownVecElement(Elem); !Held.isNull())
      {
      (void)ownScalar(ownElement(Held));  // writes the struct or the interface
      return tag("Own", structKey(ownElement(Held)->getAsCXXRecordDecl()->getDefinition()));
    }
    return type(Elem);
  }
  // Whether a type is a `std::unique_ptr` of any class.
  static bool isUniquePtr(QualType T) {
    const CXXRecordDecl *RD = T.getNonReferenceType()->getAsCXXRecordDecl();
    return RD && RD->isInStdNamespace() && RD->getIdentifier() && RD->getName() == "unique_ptr";
  }
  // The element of a unique_ptr as the type of the model: an interface is a `Struct` of its key, decision 0168.
  llvm::json::Value ownScalar(QualType Elem) const {
    if (const CXXRecordDecl *RD = Elem->getAsCXXRecordDecl(); RD && isInterface(RD)) {
      interfaceEntry(RD);
      return tag("Struct", structKey(RD->getDefinition()));
    }
    return type(Elem);
  }

  // The plain struct that a type is, decision 0073, or null. A const and a reference are looked through. Plain means a definition with
  // a name, no bases, no virtual function, no destructor and no member template, and fields that are each a scalar, a small integer
  // type (decision 0138), a plain enum (decision 0109), a plain struct, an optional of a scalar (decision 0075) or a sequence (decision
  // 0076), with no const, no reference and no bit field. Member
  // functions, static members and access do not matter, decision 0089. Nor do constructors, decision 0094: a constructor that is no
  // value constructor is refused where it is written.
  const CXXRecordDecl *plainStruct(QualType T) const {
    if (T->isReferenceType())
      T = T->getPointeeType();
    const CXXRecordDecl *RD = T.isVolatileQualified() ? nullptr : T->getAsCXXRecordDecl();
    if (!RD || !RD->hasDefinition())
      return nullptr;
    RD = RD->getDefinition();
    if (RD->isUnion() || RD->isLambda() || !RD->getIdentifier() || RD->isDependentContext() || isa<ClassTemplateSpecializationDecl>(RD) ||
        ((RD->getNumBases() || RD->isPolymorphic()) && !finalOverInterface(RD)))
      return nullptr;
    // A member function, a static member and a private field do not change the value of the struct, decision 0089. A member template still has no rule, decision 0089.
    for (const Decl *D : RD->decls())
      if (isa<FunctionTemplateDecl>(D))
        return nullptr;
    // A struct that holds a sequence of itself is in its own fields: assume it is plain there, decision 0076.
    if (!Visiting.insert(RD).second)
      return RD;
    bool Plain = true;
    for (const FieldDecl *F : RD->fields()) {
      const QualType FT = F->getType();
      if (F->isBitField() || FT->isReferenceType() || FT.hasQualifiers() ||
          (!scalar(FT) && !smallScalar(FT) && !plainEnum(FT) && !plainStruct(FT) && !optElement(FT) && seqElement(FT, true).isNull() && ownVecElement(FT).isNull())) {
        Plain = false;
        break;
      }
    }
    Visiting.erase(RD);
    return Plain ? RD : nullptr;
  }

  // Whether an expression reads the object, through `this`, implicit or written. A field of another object does not.
  static bool readsObject(const Stmt *S) {
    if (!S)
      return false;
    if (isa<CXXThisExpr>(S))
      return true;
    for (const Stmt *Child : S->children())
      if (readsObject(Child))
        return true;
    return false;
  }

  // A move constructor that the file defines, in a plain struct with no destructor of its own, decision 0179. C++ also runs it at `return x;`, for a parameter
  // by value and in a vector, where the model has no call, so it has no rule.
  bool noDestructorMove(const FunctionDecl *FD) const {
    const FunctionDecl *Def = nullptr;
    if (!isa<CXXConstructorDecl>(FD) || !FD->hasBody(Def))
      return false;
    const auto *C = cast<CXXConstructorDecl>(Def);
    // The struct table lists a destructor only when `member` holds, so a destructor `= default` is none.
    const CXXDestructorDecl *D = C->getParent()->getDestructor();
    return C->isMoveConstructor() && !C->isTemplated() && !C->isDeleted() && !C->isDefaulted() && !(D && member(D)) &&
           plainStruct(Context.getRecordType(C->getParent()));
  }

  // A constructor that is written as a function, decision 0094: a constructor of a plain struct that is no copy constructor,
  // delegates to none, and gives each field exactly one value in its member init list. It can have a body and be a move constructor, decision 0179. A field that the list leaves out
  // would take its default, which has no rule. Null for any other function. A constructor that is only declared is looked up by its definition.
  const CXXConstructorDecl *valueConstructor(const FunctionDecl *FD) const {
    const FunctionDecl *Def = nullptr;
    if (!isa<CXXConstructorDecl>(FD) || !FD->hasBody(Def))
      return nullptr;
    const auto *C = cast<CXXConstructorDecl>(Def);
    if (noDestructorMove(C))
      return nullptr;
    if (C->isTemplated() || C->getDescribedFunctionTemplate() || C->isDeleted() || C->isDefaulted() || C->isCopyConstructor() ||
        C->isDelegatingConstructor() || !plainStruct(Context.getRecordType(C->getParent())))
      return nullptr;
    if (!isa<CompoundStmt>(C->getBody()))
      return nullptr;
    std::set<const FieldDecl *> Given;
    for (const CXXCtorInitializer *Init : C->inits()) {
      // The interface bases of a final class over interfaces are built by the compiler, decision 0166.
      if (Init->isBaseInitializer() && !Init->isWritten())
        continue;
      if (!Init->isWritten() || !Init->isMemberInitializer() || !Given.insert(Init->getMember()).second || readsObject(Init->getInit()))
        return nullptr;
    }
    return Given.size() == static_cast<size_t>(std::distance(C->getParent()->field_begin(), C->getParent()->field_end())) ? C : nullptr;
  }

  // The body of a value constructor: it returns the struct, built from the values of its init list in the order of the fields.
  // A constructor with a body first computes each value of the init list into a fresh local, as C++ runs the list first. Then come the statements of the
  // body, and the struct is built from the fresh locals, decision 0179. The name of a fresh local has a `'`, which no C++ name has.
  llvm::json::Array constructorBody(const CXXConstructorDecl *C) const {
    const unsigned At = line(C->getLocation());
    const auto *Body = cast<CompoundStmt>(C->getBody());
    llvm::json::Array Out, Args;
    for (const FieldDecl *F : C->getParent()->fields())
      for (const CXXCtorInitializer *Init : C->inits())
        if (Init->getMember() == F) {
          if (Body->body_empty()) {
            Args.push_back(expr(Init->getInit(), At));
            continue;
          }
          const std::string Fresh = "'init'" + F->getNameAsString();
          Out.push_back(tag("Local", llvm::json::Array{Fresh, type(F->getType(), true), expr(Init->getInit(), At), number(At)}));
          Args.push_back(tag("Var", llvm::json::Array{Fresh, type(F->getType(), true)}));
        }
    if (!Body->body_empty()) {
      InConstructorBody = true;
      for (llvm::json::Value &One : stmts(Body))
        Out.push_back(std::move(One));
      InConstructorBody = false;
    }
    Out.push_back(tag("Return", llvm::json::Array{tag("Construct", llvm::json::Array{structKey(C->getParent()), std::move(Args)}), number(At)}));
    return Out;
  }

public:
  // An interface, decision 0165: a class in the file with no field and no base, whose members are pure virtual `const` functions and a destructor that is
  // defaulted.
  bool isInterface(const CXXRecordDecl *RD) const {
    if (!RD || !RD->hasDefinition())
      return false;
    RD = RD->getDefinition();
    if (SM.isInSystemHeader(RD->getLocation()) || RD->isUnion() || RD->isLambda() || !RD->getIdentifier() || RD->isDependentContext() || isa<ClassTemplateSpecializationDecl>(RD) ||
        RD->getNumBases() || !RD->isPolymorphic() || !RD->field_empty())
      return false;
    bool Virtual = false;
    for (const Decl *D : RD->decls()) {
      if (D->isImplicit() || isa<AccessSpecDecl>(D))
        continue;
      const auto *M = dyn_cast<CXXMethodDecl>(D);
      if (!M)
        return false;
      if (isa<CXXDestructorDecl>(M)) {
        if (!M->isDefaulted())
          return false;
        continue;
      }
      if (isa<CXXConstructorDecl>(M) || M->isStatic() || !M->isVirtual() || !M->isPureVirtual() || M->isVolatile() || M->getRefQualifier() != RQ_None ||
          M->isOverloadedOperator() || isa<CXXConversionDecl>(M))
        return false;
      Virtual = true;
    }
    return Virtual;
  }
  // The interfaces that a class derives from, or none when it has a base that is no interface, a virtual base or a base that is not public, decision 0165.
  std::vector<const CXXRecordDecl *> interfaceBases(const CXXRecordDecl *RD) const {
    std::vector<const CXXRecordDecl *> Out;
    if (!RD || !RD->hasDefinition() || RD->getNumBases() == 0 || RD->getNumVBases() != 0)
      return Out;
    for (const CXXBaseSpecifier &Base : RD->getDefinition()->bases()) {
      const CXXRecordDecl *B = Base.getType()->getAsCXXRecordDecl();
      if (Base.isVirtual() || Base.getAccessSpecifier() != AS_public || !isInterface(B))
        return {};
      Out.push_back(B->getDefinition());
    }
    return Out;
  }
  // A final class whose bases are all interfaces, decision 0165.
  bool finalOverInterface(const CXXRecordDecl *RD) const {
    return RD && RD->hasDefinition() && RD->getDefinition()->isEffectivelyFinal() && !interfaceBases(RD).empty();
  }
  // A pure virtual function of an interface, decisions 0165 and 0169. One that is not `const` writes its object.
  bool ifaceMethod(const FunctionDecl *FD) const {
    const auto *M = dyn_cast<CXXMethodDecl>(FD);
    return M && M->isPureVirtual() && isInterface(M->getParent());
  }
  // A member function, a constructor or a destructor that the model leaves out with no refusal, decision 0165: the defaulted destructor of an interface, and
  // each member of a class over an interface that is not final. A call on such a class may run an override of a subclass, so the model never reads its body.
  bool leftOut(const FunctionDecl *FD) const {
    const auto *M = dyn_cast<CXXMethodDecl>(FD);
    if (!M)
      return false;
    const CXXRecordDecl *Parent = M->getParent();
    if (isa<CXXDestructorDecl>(M) && isInterface(Parent))
      return true;
    return !interfaceBases(Parent).empty() && !finalOverInterface(Parent);
  }
  // Writes the entry of an interface in the table of structs: no field, and the member table of its virtual functions, decision 0165.
  void interfaceEntry(const CXXRecordDecl *RD) const {
    RD = RD->getDefinition();
    const std::string Key = structKey(RD);
    if (Structs.count(Key))
      return;
    Structs.emplace(Key, nullptr);
    // The members are in the order of the declarations, decision 0166: a contract reads only the functions above it.
    std::vector<std::pair<std::string, std::vector<std::string>>> Named;
    for (const Decl *D : RD->decls())
      if (const auto *M = dyn_cast<CXXMethodDecl>(D); M && ifaceMethod(M)) {
        const std::string Name = M->getNameAsString();
        auto At = std::find_if(Named.begin(), Named.end(), [&](const auto &N) { return N.first == Name; });
        if (At == Named.end())
          At = Named.insert(Named.end(), {Name, {}});
        At->second.push_back(this->key(M));
      }
    llvm::json::Array Members;
    for (const auto &[Name, Keys] : Named)
      if (Keys.size() == 1)
        Members.push_back(llvm::json::Array{Name, Keys.front()});
    const SourceLocation Loc = SM.getFileLoc(RD->getLocation());
    Structs.at(Key) = llvm::json::Object{{"struct", Key}, {"name", RD->getNameAsString()}, {"file", file(Loc)}, {"line", number(line(Loc))},
                                             {"fields", llvm::json::Array{}}, {"members", std::move(Members)}, {"interface", true},
                                             {"qualified", RD->getQualifiedNameAsString()}};
  }
  // The keys of the interfaces of a class, and the entry of each, for the table of structs, decision 0165.
  llvm::json::Array baseKeys(const CXXRecordDecl *RD) const {
    llvm::json::Array Out;
    for (const CXXRecordDecl *B : interfaceBases(RD)) {
      interfaceEntry(B);
      Out.push_back(structKey(B));
    }
    return Out;
  }
  // The entry of a class over an interface in the table of structs. A final class is a struct of 0073. One that is not final has an entry for its line only,
  // and no member, decision 0165.
  void classEntry(const CXXRecordDecl *RD) const {
    if (interfaceBases(RD).empty())
      return;
    if (finalOverInterface(RD)) {
      type(Context.getRecordType(RD));
      return;
    }
    const std::string Key = structKey(RD);
    if (Structs.count(Key))
      return;
    Structs.emplace(Key, nullptr);
    llvm::json::Array Bases = baseKeys(RD);
    const SourceLocation Loc = SM.getFileLoc(RD->getLocation());
    Structs.at(Key) = llvm::json::Object{{"struct", Key}, {"name", RD->getNameAsString()}, {"file", file(Loc)}, {"line", number(line(Loc))},
                                             {"fields", llvm::json::Array{}}, {"members", llvm::json::Array{}}, {"bases", std::move(Bases)}, {"final", false}};
  }

  // A struct with a field of a struct with a destructor is written, also when no type names it, so the core refuses the field at its line, decision 0178.
  void holderEntry(const CXXRecordDecl *RD) const {
    if (!plainStruct(Context.getRecordType(RD)))
      return;
    for (const FieldDecl *F : RD->fields())
      if (const CXXRecordDecl *Held = plainStruct(F->getType()); Held && Held->hasUserDeclaredDestructor()) {
        type(Context.getRecordType(RD));
        return;
      }
  }

  // The struct of a class with a static member function that has a contract is written, also when no type names it, decision 0174.
  void staticEntry(const CXXRecordDecl *RD) const {
    if (!plainStruct(Context.getRecordType(RD)))
      return;
    for (const Decl *D : RD->decls())
      if (const auto *M = dyn_cast<CXXMethodDecl>(D); M && listedStatic(M)) {
        type(Context.getRecordType(RD));
        return;
      }
  }

private:
  // A static member function of a plain struct, decision 0174: written as a free function with the name of its class. Null for any other function.
  const CXXMethodDecl *staticMember(const FunctionDecl *FD) const {
    const auto *M = dyn_cast<CXXMethodDecl>(FD);
    if (!M || !M->isStatic() || M->isOverloadedOperator() || M->isTemplated() || M->getDescribedFunctionTemplate())
      return nullptr;
    return plainStruct(Context.getRecordType(M->getParent())) ? M : nullptr;
  }
  // A static member function that the struct lists as a member: one with a contract that the file defines or trusts, decision 0174.
  bool listedStatic(const FunctionDecl *FD) const {
    const CXXMethodDecl *M = staticMember(FD);
    if (!M)
      return false;
    const FunctionDecl *Def = M->getDefinition();
    return (Def || trustedReason(M)) && !contractOf(SM, Def ? Def : M).Lines.empty();
  }
  // A member function that is written as a function, decision 0089: not static, not virtual, no ref-qualifier, not an operator other
  // than `operator()`, decision 0098, a conversion, a constructor or a destructor, not a template, and a member of a plain struct. Null for any other function.
  // One that is not `const` writes its object, decision 0096.
  const CXXMethodDecl *member(const FunctionDecl *FD) const {
    const auto *M = dyn_cast<CXXMethodDecl>(FD);
    if (M && ifaceMethod(M))
      return M;
    if (!M || M->isStatic() || (M->isVirtual() && !finalOverInterface(M->getParent())) || M->isVolatile() || M->isExplicitObjectMemberFunction() || M->getRefQualifier() != RQ_None || (M->isOverloadedOperator() && M->getOverloadedOperator() != OO_Call) ||
        isa<CXXConversionDecl>(M) || isa<CXXConstructorDecl>(M) || (isa<CXXDestructorDecl>(M) && (M->isDefaulted() || M->isDeleted() || M->isImplicit())) || M->isTemplated() || M->getDescribedFunctionTemplate())
      return nullptr;
    return plainStruct(Context.getRecordType(M->getParent())) ? M : nullptr;
  }
  // A member function that is `const`: pure, so a contract may call it, decision 0090.
  const CXXMethodDecl *constMember(const FunctionDecl *FD) const {
    const CXXMethodDecl *M = member(FD);
    return M && M->isConst() ? M : nullptr;
  }

  // The type of `this` in a member function of a plain struct, by the key of the struct. `ThisMut` when the function writes its object.
  llvm::json::Value thisType(const CXXRecordDecl *Parent, bool Writes = false) const {
    if (isInterface(Parent)) {
      interfaceEntry(Parent);
      return tag(Writes ? "IfaceMut" : "Iface", structKey(Parent->getDefinition()));
    }
    const CXXRecordDecl *RD = plainStruct(Context.getRecordType(Parent));
    type(Context.getRecordType(Parent));  // writes the struct
    return tag(Writes ? "ThisMut" : "This", structKey(RD));
  }

  // The key of a struct, as the key of a function that has no mangled name: the qualified name, `@` and the place of the definition.
  std::string structKey(const CXXRecordDecl *RD) const {
    const SourceLocation Loc = SM.getFileLoc(RD->getLocation());
    return RD->getQualifiedNameAsString() + "@" + file(Loc) + ":" + std::to_string(line(Loc)) + ":" + std::to_string(SM.getExpansionColumnNumber(Loc));
  }

  // The enum class of the file that a type is, decision 0109, or null: a definition in a user file, scoped, with an enumerator and no value
  // written for any. A qualified type is none, as for `scalar`.
  const EnumDecl *plainEnum(QualType T) const {
    // A const value is the same value. Any other qualifier is none, as for `scalar`.
    QualType Canon = T.getCanonicalType();
    Canon.removeLocalConst();
    if (Canon.hasQualifiers())
      return nullptr;
    const auto *Type = dyn_cast<EnumType>(Canon.getTypePtr());
    const EnumDecl *ED = Type ? Type->getDecl()->getDefinition() : nullptr;
    if (!ED || !ED->isScoped() || SM.isInSystemHeader(ED->getLocation()) || ED->enumerators().empty())
      return nullptr;
    for (const EnumConstantDecl *E : ED->enumerators())
      if (E->getInitExpr())
        return nullptr;
    return ED;
  }
  // The place of an enumerator among those of its enum, decision 0109.
  static unsigned enumeratorPlace(const EnumDecl *ED, const EnumConstantDecl *Enumerator) {
    unsigned Place = 0;
    for (const EnumConstantDecl *E : ED->enumerators()) {
      if (E == Enumerator)
        break;
      ++Place;
    }
    return Place;
  }
  // The key of an enum, as the key of a struct.
  std::string enumKey(const EnumDecl *ED) const {
    const SourceLocation Loc = SM.getFileLoc(ED->getLocation());
    return ED->getQualifiedNameAsString() + "@" + file(Loc) + ":" + std::to_string(line(Loc)) + ":" + std::to_string(SM.getExpansionColumnNumber(Loc));
  }
  // The enum as a type, written once with its enumerators in order.
  llvm::json::Value enumType(const EnumDecl *ED) const {
    const std::string Key = enumKey(ED);
    if (!Structs.count(Key)) {
      llvm::json::Array Names;
      for (const EnumConstantDecl *E : ED->enumerators())
        Names.push_back(E->getNameAsString());
      const SourceLocation Loc = SM.getFileLoc(ED->getLocation());
      Structs.emplace(Key, llvm::json::Object{{"enum", Key}, {"name", ED->getNameAsString()}, {"file", file(Loc)}, {"line", number(line(Loc))}, {"enumerators", std::move(Names)}});
    }
    return tag("Enum", Key);
  }

  // The enum class of the file that is its underlying integer, decision 0175, or null: a definition in a user file, scoped, with a fixed
  // underlying type of the subset other than bool, a value written for an enumerator, and no negative value. A qualified type is none, as for `plainEnum`.
  const EnumDecl *valuedEnum(QualType T) const {
    QualType Canon = T.getCanonicalType();
    Canon.removeLocalConst();
    if (Canon.hasQualifiers())
      return nullptr;
    const auto *Type = dyn_cast<EnumType>(Canon.getTypePtr());
    const EnumDecl *ED = Type ? Type->getDecl()->getDefinition() : nullptr;
    if (!ED || !ED->isScoped() || !ED->isFixed() || SM.isInSystemHeader(ED->getLocation()) || ED->enumerators().empty())
      return nullptr;
    const char *Under = scalar(ED->getIntegerType()) ? scalar(ED->getIntegerType()) : smallScalar(ED->getIntegerType());
    if (!Under || StringRef(Under) == "Bool")
      return nullptr;
    bool Written = false;
    for (const EnumConstantDecl *E : ED->enumerators()) {
      if (E->getInitVal().isNegative())
        return nullptr;
      Written |= E->getInitExpr() != nullptr;
    }
    return Written ? ED : nullptr;
  }
  // The valued enum as a type: its underlying integer. The line with its enumerators and their values is written once, for the contracts.
  llvm::json::Value valuedType(const EnumDecl *ED) const {
    const std::string Key = enumKey(ED);
    if (!Structs.count(Key)) {
      llvm::json::Array Values;
      for (const EnumConstantDecl *E : ED->enumerators())
        Values.push_back(llvm::json::Array{E->getNameAsString(), number(E->getInitVal().getZExtValue())});
      Structs.emplace(Key, llvm::json::Object{{"valued", ED->getNameAsString()}, {"values", std::move(Values)}});
    }
    return scalar(ED->getIntegerType()) ? llvm::json::Value(scalar(ED->getIntegerType())) : llvm::json::Value(smallScalar(ED->getIntegerType()));
  }
  // `std::chrono::milliseconds`, decision 0175: `std::chrono::duration<int64_t, std::milli>`. Any other duration is none.
  bool isMillis(QualType T) const {
    QualType Canon = T.getCanonicalType();
    Canon.removeLocalConst();
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(Canon.hasQualifiers() ? nullptr : Canon->getAsCXXRecordDecl());
    if (!Spec || Spec->getQualifiedNameAsString() != "std::chrono::duration" || Spec->getTemplateArgs().size() != 2 ||
        Spec->getTemplateArgs()[0].getKind() != TemplateArgument::Type || Spec->getTemplateArgs()[1].getKind() != TemplateArgument::Type)
      return false;
    const auto *Ratio = dyn_cast_or_null<ClassTemplateSpecializationDecl>(Spec->getTemplateArgs()[1].getAsType()->getAsCXXRecordDecl());
    if (!Ratio || Ratio->getName() != "ratio" || Ratio->getTemplateArgs().size() != 2 || Ratio->getTemplateArgs()[0].getKind() != TemplateArgument::Integral ||
        Ratio->getTemplateArgs()[1].getKind() != TemplateArgument::Integral)
      return false;
    const char *Rep = scalar(Spec->getTemplateArgs()[0].getAsType());
    return Rep && StringRef(Rep) == "I64" && Ratio->getTemplateArgs()[0].getAsIntegral() == 1 && Ratio->getTemplateArgs()[1].getAsIntegral() == 1000;
  }
  // A `std::array`, by value or by reference, with no qualifier looked at.
  static bool isStdArray(QualType T) {
    if (T->isReferenceType())
      T = T->getPointeeType();
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(T->getAsCXXRecordDecl());
    return Spec && Spec->isInStdNamespace() && Spec->getName() == "array";
  }

  // A parameter of type `T&` for a scalar or a struct of the file is `Mut(T)`, decision 0108, else null. A const reference is a value, and any other
  // reference stays `Other`.
  // A parameter `T&&` of a plain struct is the same, decision 0179. A `T&&` of anything else stays `Other`.
  llvm::json::Value mutRef(QualType T) const {
    if (!T->isReferenceType())
      return nullptr;
    const QualType Pointee = T->getPointeeType();
    if (Pointee.getCanonicalType().hasQualifiers())
      return nullptr;
    if (!T->isLValueReferenceType())
      return plainStruct(Pointee) ? tag("Mut", type(Pointee)) : llvm::json::Value(nullptr);
    if (const char *S = scalar(Pointee))
      return tag("Mut", S);
    if (plainStruct(Pointee))
      return tag("Mut", type(Pointee));
    // A reference of an interface, which a virtual function that writes may run on, decision 0169.
    if (const CXXRecordDecl *RD = Pointee->getAsCXXRecordDecl(); RD && isInterface(RD)) {
      interfaceEntry(RD);
      return tag("Mut", tag("Struct", structKey(RD->getDefinition())));
    }
    return nullptr;
  }
  // The operators that a free function may overload as a function of the model, decision 0175.
  static bool freeOperator(OverloadedOperatorKind Kind) {
    switch (Kind) {
    case OO_Plus: case OO_Minus: case OO_Star: case OO_Slash: case OO_Percent: case OO_Amp: case OO_Pipe:
    case OO_EqualEqual: case OO_ExclaimEqual: case OO_Less: case OO_LessEqual: case OO_Greater: case OO_GreaterEqual:
      return true;
    default:
      return false;
    }
  }
  // The element of a pointer to const, decisions 0140 and 0141, or null: `const T*` for a scalar or a plain struct, with no other qualifier.
  QualType constPointee(QualType T) const {
    const QualType Canon = T.getCanonicalType();
    if (!Canon->isPointerType() || Canon.hasQualifiers())
      return QualType();
    QualType Pointee = Canon->getPointeeType();
    if (!Pointee.isConstQualified())
      return QualType();
    Pointee.removeLocalConst();
    return !Pointee.hasQualifiers() && (scalar(Pointee) || plainStruct(Pointee)) ? Pointee : QualType();
  }
  // The element of a vector by reference that the function writes, decision 0145, or null: `std::vector<T>&` with no const, for a scalar `T` other
  // than bool, or a plain struct, decision 0163. A vector of bool stays `Other`.
  QualType mutSeq(QualType T) const {
    if (!T->isLValueReferenceType())
      return QualType();
    const QualType Vector = T->getPointeeType();
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(Vector->getAsCXXRecordDecl());
    if (Vector.getCanonicalType().hasQualifiers() || !Spec || !Spec->isInStdNamespace() || Spec->getName() != "vector" || Spec->getTemplateArgs().size() == 0 ||
        Spec->getTemplateArgs()[0].getKind() != TemplateArgument::Type)
      return QualType();
    return vectorElement(Spec->getTemplateArgs()[0].getAsType());
  }
  // The element of a vector that the function owns or writes: a scalar other than bool, or a plain struct, with no qualifier, or null.
  QualType vectorElement(QualType Elem, bool Owns = true) const {
    if (Elem.getCanonicalType().hasQualifiers())
      return QualType();
    if (Owns && !ownVecElement(Elem).isNull())
      return Elem;
    const char *S = scalar(Elem);
    return (S ? StringRef(S) != "Bool" : plainStruct(Elem) != nullptr) ? Elem : QualType();
  }
  // The element of a local `std::vector<T>` by value, which the function owns, decision 0160, or null: no reference, and a scalar `T` other than bool.
  // A `const` on the vector is looked through. A span is a view, not a vector, so it is none.
  QualType localVec(QualType T, bool Owns = true) const {
    if (T->isReferenceType())
      return QualType();
    const QualType Vector = T.getUnqualifiedType();
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(Vector->getAsCXXRecordDecl());
    if (T.isVolatileQualified() || !Spec || !Spec->isInStdNamespace() || Spec->getName() != "vector" || Spec->getTemplateArgs().size() == 0 ||
        Spec->getTemplateArgs()[0].getKind() != TemplateArgument::Type)
      return QualType();
    return vectorElement(Spec->getTemplateArgs()[0].getAsType(), Owns);
  }
  // Whether an expression names a vector that the function writes: a vector by reference, decision 0145, or a local vector, decision 0160.
  bool isMutSeq(const Expr *E) const {
    const auto *Ref = dyn_cast<DeclRefExpr>(E->IgnoreParenImpCasts());
    if (!Ref)
      return false;
    if (isa<ParmVarDecl>(Ref->getDecl()))
      return !mutSeq(Ref->getDecl()->getType()).isNull();
    const auto *Var = dyn_cast<VarDecl>(Ref->getDecl());
    return Var && Var->hasLocalStorage() && !localVec(Var->getType()).isNull();
  }
  // The type of a parameter, or of a name that reads one. A pointer to const is a `Ptr` of what it points to, decisions 0140 and 0141.
  llvm::json::Value paramType(QualType T) const {
    llvm::json::Value Written = mutRef(T);
    if (!Written.getAsNull())
      return Written;
    if (const QualType Element = constPointee(T); !Element.isNull())
      return tag("Ptr", type(Element));
    if (const QualType Element = mutSeq(T); !Element.isNull())
      return tag("MutSeq", elementType(Element));
    // A `unique_ptr` parameter is read by const reference only, decision 0142. By value it has no rule: it moves.
    if (T->isLValueReferenceType() && T->getPointeeType().isConstQualified())
      if (const QualType Element = ownElement(T->getPointeeType()); !Element.isNull())
        return tag("Own", ownScalar(Element));
    // By value, a unique_ptr of a struct or an interface is a value that the function owns, decision 0171.
    if (!ownVecElement(T).isNull() && !T.isConstQualified())
      return tag("Own", ownScalar(ownElement(T)));
    if (isOwn(T))
      return tag("Other", T.getAsString(Context.getPrintingPolicy()));
    // A parameter `const B&` of an interface is a value of the interface, decision 0165. A pointer, a local, a result and a field have no rule.
    if (T->isLValueReferenceType() && T->getPointeeType().isConstQualified())
      if (const CXXRecordDecl *RD = T->getPointeeType()->getAsCXXRecordDecl(); RD && isInterface(RD)) {
        interfaceEntry(RD);
        return tag("IfaceRef", structKey(RD->getDefinition()));
      }
    // A parameter `const T&` of a scalar `T` is the scalar by value, decision 0175.
    if (T->isLValueReferenceType() && T->getPointeeType().isConstQualified()) {
      const QualType Pointee = T->getPointeeType().getUnqualifiedType();
      if (scalar(Pointee) || smallScalar(Pointee))
        return type(Pointee);
    }
    return type(T);
  }
  // The type of a result. A `std::vector<T>` by value with no qualifier is a `Vec`, decision 0163: the function gives a copy. A span stays `Other`.
  llvm::json::Value resultType(QualType T) const {
    if (!T.hasQualifiers())
      if (const QualType Element = localVec(T, false); !Element.isNull())
        return tag("Vec", type(Element));
    return type(T);
  }
  // The loop variable of a range-for has the element type whether it is `const` or a const reference, decision 0143. The loop is written only
  // when that type is the element's.
  llvm::json::Value varType(const ValueDecl *D) const {
    if (const auto *Var = dyn_cast<VarDecl>(D); Var && Var->isCXXForRangeDecl())
      return type(Var->getType().getNonReferenceType().getUnqualifiedType());
    // A local vector is a `Vec`, decision 0160.
    if (const auto *Var = dyn_cast<VarDecl>(D); Var && Var->hasLocalStorage() && !isa<ParmVarDecl>(Var))
      if (const QualType Element = localVec(Var->getType()); !Element.isNull())
        return tag("Vec", elementType(Element));
    // A `const` on a local changes no value of the model, decision 0166.
    if (const auto *Var = dyn_cast<VarDecl>(D); Var && Var->hasLocalStorage() && !isa<ParmVarDecl>(Var) && !Var->getType()->isReferenceType() && !Var->isCXXForRangeDecl() &&
                                                 Var->getType().isLocalConstQualified()) {
      QualType Plain = Var->getType();
      Plain.removeLocalConst();
      if (scalar(Plain) || smallScalar(Plain) || plainEnum(Plain) || valuedEnum(Plain) || isMillis(Plain))
        return type(Plain);
    }
    // The parameter of a lambda is the element, whether it is by value or by const reference, decision 0149.
    if (const auto *Param = dyn_cast<ParmVarDecl>(D); Param && isa<CXXMethodDecl>(Param->getDeclContext()) && cast<CXXMethodDecl>(Param->getDeclContext())->getParent()->isLambda())
      return type(Param->getType().getNonReferenceType().getUnqualifiedType());
    return isa<ParmVarDecl>(D) ? paramType(D->getType()) : type(D->getType());
  }

  llvm::json::Value type(QualType T, bool Field = false) const {
    if (const char *S = scalar(T))
      return S;
    if (const char *S = smallScalar(T))
      return S;
    if (const EnumDecl *ED = plainEnum(T))
      return enumType(ED);
    if (const EnumDecl *ED = valuedEnum(T))
      return valuedType(ED);
    // A duration in milliseconds is its count, decision 0175.
    if (isMillis(T))
      return "I64";
    // A `double` by value is a real that only compares, decision 0150. A field, a sequence, an optional and a reference of it stay out.
    if (!Field && isDouble(T))
      return "F64";
    // Decision 0074: a struct is by value or by const lvalue reference. Any other reference stays `Other`.
    const bool Writable = T->isReferenceType() && !(T->isLValueReferenceType() && T->getPointeeType().isConstQualified());
    if (const CXXRecordDecl *RD = Writable ? nullptr : plainStruct(T)) {
      const std::string Key = structKey(RD);
      if (!Structs.count(Key)) {
        Structs.emplace(Key, nullptr);  // a recursive struct finds itself here, decision 0076
        llvm::json::Array Fields;
        for (const FieldDecl *F : RD->fields())
          Fields.push_back(llvm::json::Array{F->getNameAsString(), type(F->getType(), true)});
        // The member functions that are written as functions, as (name, key), decision 0090. A name that two of them share is left out:
        // a contract cannot tell the overloads apart, so it calls none.
        std::map<std::string, std::vector<std::string>> Named;
        for (const Decl *D : RD->decls())
          // An override that writes its object is a member too, so the check finds it. A contract cannot call it, decision 0169.
          if (const auto *M = dyn_cast<CXXMethodDecl>(D); M && (constMember(M) || (M->isVirtual() && member(M)) || (isa<CXXDestructorDecl>(M) && member(M))))
            Named[isa<CXXDestructorDecl>(M) ? "~" : M->getNameAsString()].push_back(key(M));
        // The static member functions with a contract, under their qualified names, decision 0174.
        for (const Decl *D : RD->decls())
          if (const auto *M = dyn_cast<CXXMethodDecl>(D); M && listedStatic(M))
            Named[name(M)].push_back(key(M));
        llvm::json::Array Members;
        for (const auto &[Name, Keys] : Named)
          if (Keys.size() == 1)
            Members.push_back(llvm::json::Array{Name, Keys.front()});
        const SourceLocation Loc = SM.getFileLoc(RD->getLocation());
        llvm::json::Object Entry{{"struct", Key}, {"name", RD->getNameAsString()}, {"file", file(Loc)}, {"line", number(line(Loc))},
                                 {"fields", std::move(Fields)}, {"members", std::move(Members)}};
        // A final class over interfaces names them, decision 0165.
        if (finalOverInterface(RD)) {
          Entry["bases"] = baseKeys(RD);
          Entry["final"] = true;
        }
        Structs.at(Key) = std::move(Entry);
      }
      return tag("Struct", Key);
    }
    if (const QualType E = seqElement(T, Field); !E.isNull())
      return tag("Seq", llvm::json::Array{elementType(E), seqExtent(T)});
    if (const QualType E = optType(T); !E.isNull())
      return tag("Opt", type(E));
    // A field holds a unique_ptr of a struct or an interface, decision 0171.
    if (const QualType E = Field ? (ownVecElement(T).isNull() ? QualType() : ownElement(T)) : ownElement(T); !E.isNull())
      return tag("Own", ownScalar(E));
    return tag("Other", T.getAsString(Context.getPrintingPolicy()));
  }

  // The statements of a branch or of the body: a compound statement is its list, and any other statement is a list of one.
  llvm::json::Array stmts(const Stmt *S) const {
    llvm::json::Array Out;
    if (const auto *Block = dyn_cast<CompoundStmt>(S))
      for (const Stmt *Child : Block->body()) {
        bodyLines(Child, Out);
        Out.push_back(stmt(Child));
      }
    else {
      bodyLines(S, Out);
      Out.push_back(stmt(S));
    }
    return Out;
  }

  llvm::json::Value stmt(const Stmt *S) const {
    // The body of a constructor cannot read or write a field, or use `this`, and it cannot return early, decision 0179. A control statement holds its
    // expressions and its statements, which come here or to `expr` themselves.
    if (InConstructorBody && !isa<IfStmt, WhileStmt, ForStmt, CXXForRangeStmt, SwitchStmt, CompoundStmt, DoStmt>(S)) {
      if (readsObject(S))
        return unknown(S, "a field in the body of a constructor", line(S->getBeginLoc()));
      if (isa<ReturnStmt>(S))
        return unknown(S, describe(S), line(S->getBeginLoc()));
    }
    if (const auto *If = dyn_cast<IfStmt>(S); If && !If->getInit() && !If->getConditionVariable() && !If->isConsteval())
      return tag("If", llvm::json::Array{expr(If->getCond(), line(S->getBeginLoc())), stmts(If->getThen()), If->getElse() ? stmts(If->getElse()) : llvm::json::Array{},
                                         number(line(S->getBeginLoc()))});
    if (const auto *Return = dyn_cast<ReturnStmt>(S); Return && !Return->getRetValue())
      return tag("Exit", number(line(S->getBeginLoc())));
    // `return f();` of a void call has no rule: the return gives no value.
    if (const auto *Return = dyn_cast<ReturnStmt>(S); Return && Return->getRetValue() && Return->getRetValue()->getType()->isVoidType())
      return unknown(S, describe(S), line(S->getBeginLoc()));
    if (const auto *Return = dyn_cast<ReturnStmt>(S); Return && Return->getRetValue())
      return tag("Return", llvm::json::Array{expr(Return->getRetValue(), line(S->getBeginLoc())), number(line(S->getBeginLoc()))});
    if (const auto *Switch = dyn_cast<SwitchStmt>(S); Switch && !Switch->getInit() && !Switch->getConditionVariable() && plainEnum(Switch->getCond()->IgnoreParenImpCasts()->getType()))
      return switchOf(Switch);
    if (const auto *Decl = dyn_cast<DeclStmt>(S); Decl && Decl->isSingleDecl())
      if (const auto *Var = dyn_cast<VarDecl>(Decl->getSingleDecl()); Var && Var->hasLocalStorage() && Var->getInit())
        return tag("Local", llvm::json::Array{Var->getNameAsString(), varType(Var), expr(Var->getInit(), line(S->getBeginLoc())), number(line(S->getBeginLoc()))});
    if (const auto *Assign = dyn_cast<BinaryOperator>(S); Assign && Assign->getOpcode() == BO_Assign) {
      if (const auto *Target = dyn_cast<DeclRefExpr>(Assign->getLHS()); Target && isTarget(Target->getDecl()))
        return tag("Assign", llvm::json::Array{nameOf(Target->getDecl()), expr(Assign->getRHS(), line(S->getBeginLoc())), number(line(S->getBeginLoc()))});
      // `v[i] = e` where `v` is a vector by reference, decision 0145. Any other write to a vector has no rule.
      if (const auto *Subscript = dyn_cast<CXXOperatorCallExpr>(Assign->getLHS()->IgnoreParens());
          Subscript && Subscript->getOperator() == OO_Subscript && Subscript->getNumArgs() == 2 && isMutSeq(Subscript->getArg(0)))
        return tag("SetIndex", llvm::json::Array{cast<DeclRefExpr>(Subscript->getArg(0)->IgnoreParenImpCasts())->getDecl()->getNameAsString(),
                                                 expr(Subscript->getArg(1), line(S->getBeginLoc())), expr(Assign->getRHS(), line(S->getBeginLoc())),
                                                 number(line(S->getBeginLoc()))});
      // A write of a field of a reference parameter, decision 0108.
      if (const auto [Param, Field] = refField(Assign->getLHS()); Param)
        return tag("SetRefField", llvm::json::Array{Param->getNameAsString(), Field->getNameAsString(), expr(Assign->getRHS(), line(S->getBeginLoc())), number(line(S->getBeginLoc()))});
      // A write of a field of the object, decision 0096.
      if (const FieldDecl *Field = objectField(Assign->getLHS()))
        return tag("SetField", llvm::json::Array{Field->getNameAsString(), expr(Assign->getRHS(), line(S->getBeginLoc())), number(line(S->getBeginLoc()))});
    }
    // `v[i] = e` on a vector of unique_ptr has no rule yet, decision 0170.
    {
      const Stmt *Plain = S;
      if (const auto *Cleanups = dyn_cast<ExprWithCleanups>(Plain))
        Plain = Cleanups->getSubExpr();
      if (const auto *Assign = dyn_cast<CXXOperatorCallExpr>(Plain); Assign && Assign->getOperator() == OO_Equal && Assign->getNumArgs() == 2 && isUniquePtr(Assign->getArg(0)->getType()))
        if (const auto *Element = dyn_cast<CXXOperatorCallExpr>(Assign->getArg(0)->IgnoreParenImpCasts()); Element && Element->getOperator() == OO_Subscript)
          return unknown(S, "an assignment to a unique_ptr element", line(S->getBeginLoc()));
    }
    // `x = y` for a struct, with the copy assignment that the compiler makes, is the write of the variable, decision 0108.
    if (const auto *Copy = dyn_cast<CXXOperatorCallExpr>(S); Copy && Copy->getOperator() == OO_Equal && Copy->getNumArgs() == 2 && plainStruct(Copy->getArg(0)->getType()) &&
                                                             Copy->getDirectCallee() && Copy->getDirectCallee()->isTrivial())
      if (const auto *Target = dyn_cast<DeclRefExpr>(Copy->getArg(0)->IgnoreParens()); Target && isTarget(Target->getDecl()))
        return tag("Assign", llvm::json::Array{nameOf(Target->getDecl()), expr(Copy->getArg(1), line(S->getBeginLoc())), number(line(S->getBeginLoc()))});
    // `x op= e` for `+ - * / %` on an integer local or a field of the object is `x = x op e`, with the conversions that the compiler made,
    // decision 0096.
    if (const auto *Compound = dyn_cast<CompoundAssignOperator>(S)) {
      if (llvm::json::Value Lowered = compound(Compound); !Lowered.getAsNull())
        return Lowered;
    }
    // A temporary for a computed or literal argument wraps a call in a cleanup. The statement is the call inside it.
    const Stmt *Inner = S;
    if (const auto *Cleanups = dyn_cast<ExprWithCleanups>(Inner))
      Inner = Cleanups->getSubExpr();
    // A call that gives a struct with a destructor is bound as a temporary. The bind is not the call, decision 0178.
    if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(Inner))
      if (const CXXRecordDecl *RD = plainStruct(Bound->getType()); RD && RD->hasUserDeclaredDestructor())
        Inner = Bound->getSubExpr();
    // `v.push_back(e)` where `v` is a vector by reference, decision 0148. The other member calls of a vector have no rule.
    if (const auto *Push = dyn_cast<CXXMemberCallExpr>(Inner); Push && Push->getNumArgs() == 1 && Push->getMethodDecl() && Push->getMethodDecl()->getDeclName().isIdentifier() &&
                                                           Push->getMethodDecl()->getName() == "push_back" && Push->getImplicitObjectArgument() &&
                                                           isMutSeq(Push->getImplicitObjectArgument())) {
      // The argument is bound to a reference, so a computed value sits in a temporary that is not the value.
      const Expr *Arg = Push->getArg(0);
      if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Arg))
        Arg = Temporary->getSubExpr();
      llvm::json::Value Pushed = expr(Arg, line(S->getBeginLoc()));
      // The conversion of `std::make_unique<D>(a)` to the unique_ptr of the interface stands as the `Wrap` alone, decision 0170.
      if (llvm::json::Object *Outer = Pushed.getAsObject())
        if (llvm::json::Array *Casted = Outer->getArray("Cast"); Casted && Casted->size() == 2 && (*Casted)[0].getAsString() == StringRef("Construct"))
          if (const llvm::json::Object *Inner = (*Casted)[1].getAsObject(); Inner && Inner->get("Wrap")) {
            llvm::json::Value Bare = std::move((*Casted)[1]);
            Pushed = std::move(Bare);
          }
      return tag("PushBack", llvm::json::Array{cast<DeclRefExpr>(Push->getImplicitObjectArgument()->IgnoreParenImpCasts())->getDecl()->getNameAsString(),
                                               std::move(Pushed), number(line(S->getBeginLoc()))});
    }
    // A call that is the whole statement, `f(a);` or `o.f(a);`. Its object is the first argument, decision 0096.
    // `std::sort(v.begin(), v.end())` of a vector that the function writes is a sort of the whole of `v`, decision 0161. A comparator lambda of the element type
    // with one return is `SortBy`, decision 0162. Any other call of `std::sort`, a part of a range, another comparator, a policy or two vectors, is named by
    // what it is.
    if (const auto *Sort = dyn_cast<CallExpr>(Inner); Sort && Sort->getStmtClass() == Stmt::CallExprClass && Sort->getDirectCallee() &&
                                                       Sort->getDirectCallee()->isInStdNamespace() && Sort->getDirectCallee()->getDeclName().isIdentifier() &&
                                                       Sort->getDirectCallee()->getName() == "sort" && SM.isInSystemHeader(Sort->getDirectCallee()->getLocation())) {
      const VarDecl *Whole = nullptr;
      bool Same = Sort->getNumArgs() == 2 || Sort->getNumArgs() == 3;
      for (unsigned I = 0; Same && I < 2; ++I) {
        const auto *Member = dyn_cast<CXXMemberCallExpr>(Sort->getArg(I)->IgnoreParenImpCasts());
        const Expr *Object = Member ? Member->getImplicitObjectArgument() : nullptr;
        const auto *Ref = Object ? dyn_cast<DeclRefExpr>(Object->IgnoreParenImpCasts()) : nullptr;
        const auto *Var = Ref ? dyn_cast<VarDecl>(Ref->getDecl()) : nullptr;
        Same = Member && Member->getNumArgs() == 0 && Member->getMethodDecl() && Member->getMethodDecl()->getDeclName().isIdentifier() &&
               Member->getMethodDecl()->getName() == (I == 0 ? "begin" : "end") && Var && (isa<ParmVarDecl>(Var) || Var->hasLocalStorage()) && (!Whole || Whole == Var);
        Whole = Var;
      }
      if (Same && Sort->getNumArgs() == 2)
        return tag("Sort", llvm::json::Array{Whole->getNameAsString(), number(line(S->getBeginLoc()))});
      // A comparator lambda with two parameters of one type, decision 0162. The core compares that type with the element.
      if (Same && Sort->getNumArgs() == 3)
        if (const LambdaExpr *Lambda = lambdaArgument(Sort->getArg(2)); Lambda && Lambda->getCallOperator()->getNumParams() == 2)
          if (const ReturnStmt *Return = lambdaReturn(Lambda)) {
            const CXXMethodDecl *Operator = Lambda->getCallOperator();
            const QualType First = comparatorParameter(Operator->getParamDecl(0)), Second = comparatorParameter(Operator->getParamDecl(1));
            if (!First.isNull() && First == Second)
              return tag("SortBy", llvm::json::Array{Whole->getNameAsString(), Operator->getParamDecl(0)->getNameAsString(), Operator->getParamDecl(1)->getNameAsString(), type(First),
                                                     expr(Return->getRetValue(), line(S->getBeginLoc())), number(line(S->getBeginLoc()))});
          }
      return unknown(S, "std::sort of another form", line(S->getBeginLoc()));
    }
    // A call of a destructor in code destroys the object a second time at the end of its block, decision 0178.
    if (const auto *Member = dyn_cast<CXXMemberCallExpr>(Inner); Member && Member->getMethodDecl() && isa<CXXDestructorDecl>(Member->getMethodDecl()))
      return unknown(S, "a call of a destructor", line(S->getBeginLoc()));
    if (const auto *Call = dyn_cast<CallExpr>(Inner)) {
      if (llvm::json::Value Written = expr(Call, line(S->getBeginLoc())); Written.getAsObject() && Written.getAsObject()->get("Call"))
        return Written;
      // The call with a class at a reference of its interface says why, decision 0169.
      else if (const llvm::json::Array *Why = Written.getAsObject() ? Written.getAsObject()->getArray("Unknown") : nullptr;
               Why && !Why->empty() && (*Why)[0].getAsString() == StringRef("a class as a reference to its interface"))
        return Written;
    }
    // A bare block `{ ... }` is a block of the model, decision 0178.
    if (const auto *Bare = dyn_cast<CompoundStmt>(S))
      return tag("Block", llvm::json::Array{stmts(Bare), number(line(S->getBeginLoc()))});
    if (const auto *Step = dyn_cast<UnaryOperator>(S); Step && Step->isIncrementDecrementOp())
      if (const auto *Target = dyn_cast<DeclRefExpr>(Step->getSubExpr()); Target && isTarget(Target->getDecl()))
        return tag("Step", llvm::json::Array{nameOf(Target->getDecl()), varType(Target->getDecl()), Step->isIncrementOp(),
                                             number(line(S->getBeginLoc()))});
    if (const auto *While = dyn_cast<WhileStmt>(S); While && !While->getConditionVariable())
      return tag("While", llvm::json::Array{expr(While->getCond(), line(S->getBeginLoc())), loopConds(S), stmts(While->getBody()), number(line(S->getBeginLoc()))});
    // A range-for over a read-only sequence parameter, decision 0143. The loop variable is `T x`, `const T& x`, `auto x` or `const auto& x`, with
    // `T` the element type. The core builds the loop over the indexes. A write reference, a range that is no parameter, and an element of
    // another type stay unknown.
    // A range over a vector of unique_ptr has no rule yet, decision 0170.
    if (const auto *Range = dyn_cast<CXXForRangeStmt>(S)) {
      const auto *Named = dyn_cast<DeclRefExpr>(Range->getRangeInit()->IgnoreParenImpCasts());
      const QualType Held = Named ? Named->getDecl()->getType() : Range->getRangeInit()->getType();
      if (!ownVecElement(seqElement(Held)).isNull() || !ownVecElement(mutSeq(Held)).isNull() || !ownVecElement(localVec(Held.getNonReferenceType())).isNull())
        return unknown(S, "a range-for over a vector of unique_ptr", line(S->getBeginLoc()));
    }
    if (const auto *Range = dyn_cast<CXXForRangeStmt>(S); Range && !Range->getInit() && Range->getLoopVariable() && Range->getLoopVariable()->getIdentifier())
      if (const auto *Ref = dyn_cast<DeclRefExpr>(Range->getRangeInit()->IgnoreParenImpCasts()); Ref && isa<ParmVarDecl>(Ref->getDecl()) && isSeq(Ref->getType())) {

        QualType Declared = Range->getLoopVariable()->getType();
        bool Written = false;
        if (Declared->isReferenceType()) {
          Written = !Declared->isLValueReferenceType() || !Declared->getPointeeType().isConstQualified();
          Declared = Declared->getPointeeType();
        }
        const QualType Element = seqElement(Ref->getType());
        if (!Written && Declared.getCanonicalType().getUnqualifiedType() == Element.getCanonicalType().getUnqualifiedType())
          return tag("RangeFor", llvm::json::Array{Range->getLoopVariable()->getNameAsString(), type(Element), expr(Ref, line(S->getBeginLoc())), loopConds(S),
                                                   stmts(Range->getBody()), number(line(S->getBeginLoc()))});
      }
    // A local of a struct with a destructor in the head of a `for` has no rule, decision 0178.
    if (const auto *For = dyn_cast<ForStmt>(S))
      if (const auto *Init = dyn_cast_or_null<DeclStmt>(For->getInit()))
        for (const Decl *D : Init->decls())
          if (const auto *Var = dyn_cast<VarDecl>(D))
            if (const CXXRecordDecl *RD = plainStruct(Var->getType()); RD && RD->hasUserDeclaredDestructor())
              return unknown(S, describe(S), line(S->getBeginLoc()));
    if (const auto *For = dyn_cast<ForStmt>(S); For && For->getCond() && For->getInc() && !For->getConditionVariable())
      if (const auto *Init = dyn_cast_or_null<DeclStmt>(For->getInit()); Init && Init->isSingleDecl())
        if (const auto *Var = dyn_cast<VarDecl>(Init->getSingleDecl()); Var && Var->hasLocalStorage() && Var->getInit())
          return tag("For", llvm::json::Array{stmt(Init), expr(For->getCond(), line(S->getBeginLoc())), stmt(For->getInc()), loopConds(S),
                                              stmts(For->getBody()), number(line(S->getBeginLoc()))});
    return unknown(S, describe(S), line(S->getBeginLoc()));
  }

  // A switch over a value of an enum, decision 0109: the cases in source order, each with the place of its enumerator and its statements up to the
  // next label. A `break` that ends a case is dropped. A default, a label with another label for its body, and anything before the first label stay
  // unknown, by their nodes.
  llvm::json::Value switchOf(const SwitchStmt *Switch) const {
    const unsigned At = line(Switch->getBeginLoc());
    const auto *Body = dyn_cast_or_null<CompoundStmt>(Switch->getBody());
    if (!Body)
      return unknown(Switch, describe(Switch), At);
    const EnumDecl *ED = plainEnum(Switch->getCond()->IgnoreParenImpCasts()->getType());
    enumType(ED);
    llvm::json::Array Cases;
    std::vector<const Stmt *> Current;
    const auto close = [&]() {
      // A body in braces, with the break after them or inside them, is the statements of the block, decision 0114. Any other shape stays as it is.
      if (!Current.empty() && isa<CompoundStmt>(Current.front()) && (Current.size() == 1 || (Current.size() == 2 && isa<BreakStmt>(Current.back())))) {
        const auto Block = cast<CompoundStmt>(Current.front())->body();
        Current.assign(Block.begin(), Block.end());
      }
      if (!Current.empty() && isa<BreakStmt>(Current.back()))
        Current.pop_back();
      llvm::json::Array Out;
      for (const Stmt *Child : Current) {
        bodyLines(Child, Out);
        Out.push_back(stmt(Child));
      }
      Cases.back().getAsArray()->push_back(std::move(Out));
      Current.clear();
    };
    for (const Stmt *Child : Body->body()) {
      if (isa<DefaultStmt>(Child) || (isa<CaseStmt>(Child) && (isa<CaseStmt>(cast<CaseStmt>(Child)->getSubStmt()) || isa<DefaultStmt>(cast<CaseStmt>(Child)->getSubStmt()))))
        return unknown(Child, describe(isa<CaseStmt>(Child) ? cast<CaseStmt>(Child)->getSubStmt() : Child), line(Child->getBeginLoc()));
      if (const auto *Label = dyn_cast<CaseStmt>(Child)) {
        const auto *Name = dyn_cast<DeclRefExpr>(Label->getLHS()->IgnoreParenImpCasts());
        const auto *Enumerator = Name ? dyn_cast<EnumConstantDecl>(Name->getDecl()) : nullptr;
        if (!Enumerator || Enumerator->getDeclContext() != ED || Label->getRHS())
          return unknown(Child, describe(Child), line(Child->getBeginLoc()));
        if (!Cases.empty())
          close();
        Cases.push_back(llvm::json::Array{number(enumeratorPlace(ED, Enumerator))});
        Current.push_back(Label->getSubStmt());
      } else if (Cases.empty()) {
        return unknown(Child, describe(Child), line(Child->getBeginLoc()));
      } else {
        Current.push_back(Child);
      }
    }
    if (!Cases.empty())
      close();
    return tag("Switch", llvm::json::Array{expr(Switch->getCond()->IgnoreParenImpCasts(), At), enumKey(ED), std::move(Cases), number(At)});
  }

  // A field of a struct reference parameter, `p.f`, as the parameter and the field, or two nulls, decision 0108.
  std::pair<const ParmVarDecl *, const FieldDecl *> refField(const Expr *E) const {
    if (const auto *Member = dyn_cast<MemberExpr>(E->IgnoreParens()); Member && !Member->isArrow())
      if (const auto *Base = dyn_cast<DeclRefExpr>(Member->getBase()->IgnoreParenImpCasts()))
        if (const auto *Param = dyn_cast<ParmVarDecl>(Base->getDecl()); Param && !mutRef(Param->getType()).getAsNull())
          if (const auto *Field = dyn_cast<FieldDecl>(Member->getMemberDecl()); Field && plainStruct(Context.getRecordType(Field->getParent())))
            return {Param, Field};
    return {nullptr, nullptr};
  }

  // The field of a plain struct that an expression names on the object of a member function, `n_` or `this->n_`, or null.
  const FieldDecl *objectField(const Expr *E) const {
    if (const auto *Member = dyn_cast<MemberExpr>(E->IgnoreParens()); Member && isa<CXXThisExpr>(Member->getBase()->IgnoreParenImpCasts()))
      if (const auto *Field = dyn_cast<FieldDecl>(Member->getMemberDecl()); Field && plainStruct(Context.getRecordType(Field->getParent())))
        return Field;
    return nullptr;
  }

  // `x op= e` as the write `x = x op e`, or null when it has no rule. The left side is read, converted to the computation type, operated on,
  // and converted back, as the compiler does. The right side is already in the computation type.
  llvm::json::Value compound(const CompoundAssignOperator *C) const {
    const char *Op = nullptr;
    switch (C->getOpcode()) {
    case BO_AddAssign: Op = "Add"; break;
    case BO_SubAssign: Op = "Sub"; break;
    case BO_MulAssign: Op = "Mul"; break;
    case BO_DivAssign: Op = "Div"; break;
    case BO_RemAssign: Op = "Rem"; break;
    default: return nullptr;
    }
    const unsigned At = line(C->getBeginLoc());
    const Expr *Left = C->getLHS();
    const char *Scalar = scalar(Left->getType());
    // `x += e` of a double is the write of `x + e`, which the core refuses as a rounding, decision 0150.
    if (!isDouble(Left->getType()) && (!Scalar || StringRef(Scalar) == "Bool"))
      return nullptr;
    const auto *Name = dyn_cast<DeclRefExpr>(Left);
    const FieldDecl *Field = Name ? nullptr : objectField(Left);
    const auto [Param, RefField] = Name ? std::pair<const ParmVarDecl *, const FieldDecl *>{} : refField(Left);
    if (!(Name && isTarget(Name->getDecl())) && !Field && !Param)
      return nullptr;
    const auto convert = [&](llvm::json::Value V, QualType From, QualType To) -> llvm::json::Value {
      if (Context.hasSameType(From, To))
        return V;
      return tag("Cast", llvm::json::Array{tag("Integral", llvm::json::Array{type(From), type(To)}), std::move(V)});
    };
    llvm::json::Value Read = tag("Cast", llvm::json::Array{"Read", expr(Left, At)});
    llvm::json::Value A = convert(std::move(Read), Left->getType(), C->getComputationLHSType());
    llvm::json::Value B = expr(C->getRHS(), At);
    llvm::json::Value Operated =
        StringRef(Op) == "Div" || StringRef(Op) == "Rem"
            ? tag("Divide", llvm::json::Array{Op, std::move(A), std::move(B), type(C->getComputationResultType())})
            : tag("Bin", llvm::json::Array{Op, std::move(A), std::move(B)});
    llvm::json::Value Value = convert(std::move(Operated), C->getComputationResultType(), Left->getType());
    if (Param)
      return tag("SetRefField", llvm::json::Array{Param->getNameAsString(), RefField->getNameAsString(), std::move(Value), number(At)});
    if (Field)
      return tag("SetField", llvm::json::Array{Field->getNameAsString(), std::move(Value), number(At)});
    return tag("Assign", llvm::json::Array{nameOf(Name->getDecl()), std::move(Value), number(At)});
  }

  // A parameter or a local: the names the translator reads and writes.
  static bool isVariable(const ValueDecl *D) { return isa<ParmVarDecl>(D) || (isa<VarDecl>(D) && cast<VarDecl>(D)->hasLocalStorage()); }
  // A variable or a global: the names that a write can target, decision 0173.
  static bool isTarget(const ValueDecl *D) { return isVariable(D) || isGlobal(D); }

  // The optional that a read names, decision 0133. The compiler holds the optional that a call or a construction gives in a temporary, and
  // the read names the temporary. A reference local is refused, row lvalue_references, so the read is always copied into a value and no
  // reference outlives the temporary. Used at these reads only.
  static const Expr *optObject(const Expr *E) {
    const Expr *Inner = E;
    bool Held = false;
    for (;;) {
      if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Inner))
        Inner = Temporary->getSubExpr(), Held = true;
      else if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(Inner))
        Inner = Bound->getSubExpr(), Held = true;
      else if (const auto *Cast = dyn_cast<ImplicitCastExpr>(Inner); Cast && Cast->getCastKind() == CK_NoOp)
        Inner = Cast->getSubExpr();
      else
        return Held ? Inner : E;
    }
  }

  // A positive double as `m * 2^p` with `m` odd, or zero as (0, 0).
  static void splitDouble(double Value, uint64_t &Mantissa, int &Power) {
    int Exponent = 0;
    const double Fraction = std::frexp(Value, &Exponent);
    Mantissa = static_cast<uint64_t>(std::ldexp(Fraction, 53));
    Power = Exponent - 53;
    while (Mantissa && Mantissa % 2 == 0)
      Mantissa /= 2, ++Power;
  }
  // The value of a non-negative double as `m / q` with `q` a power of two and both in 64 bits, or false, decision 0158.
  static bool dyadic(double Value, uint64_t &M, uint64_t &Q) {
    uint64_t Mantissa;
    int Power;
    splitDouble(Value, Mantissa, Power);
    if (!Mantissa)
      return M = 0, Q = 1, true;
    if (Power >= 0) {
      const unsigned __int128 Whole = static_cast<unsigned __int128>(Mantissa) << (Power < 64 ? Power : 64);
      return Power < 64 && Whole <= UINT64_MAX ? (M = static_cast<uint64_t>(Whole), Q = 1, true) : false;
    }
    return -Power <= 63 ? (M = Mantissa, Q = uint64_t(1) << -Power, true) : false;
  }
  // The expression of a double value, or null when no form fits: `RealLit` for `d / 10^k` with `k` up to 19 and `d` in 64 bits, decision 0150, else
  // `Ratio` for `m / q`, decision 0158. A negative value is the negation of one.
  llvm::json::Value realForm(double Value) const {
    if (!std::isfinite(Value))
      return nullptr;
    if (std::signbit(Value) && Value != 0.0) {
      llvm::json::Value Inner = realForm(-Value);
      return Inner.getAsNull() ? Inner : tag("Neg", std::move(Inner));
    }
    uint64_t Mantissa;
    int Power;
    splitDouble(Value, Mantissa, Power);
    if (!Mantissa)
      return tag("RealLit", llvm::json::Array{number(0), number(0)});
    unsigned __int128 Digits = Mantissa;
    if (Power >= 0) {
      if (Power < 64 && (Digits << Power) <= UINT64_MAX)
        return tag("RealLit", llvm::json::Array{number(static_cast<uint64_t>(Digits << Power)), number(0)});
      return nullptr;
    }
    if (-Power <= 19) {
      for (int I = 0; I < -Power && Digits <= UINT64_MAX; ++I)
        Digits *= 5;
      if (Digits <= UINT64_MAX)
        return tag("RealLit", llvm::json::Array{number(static_cast<uint64_t>(Digits)), number(-Power)});
    }
    uint64_t M, Q;
    return dyadic(Value, M, Q) ? tag("Ratio", llvm::json::Array{number(M), number(Q)}) : llvm::json::Value(nullptr);
  }

  // The lambda written in a call, behind the copies and temporaries that the compiler adds, or null.
  static const LambdaExpr *lambdaArgument(const Expr *Arg) {
    for (;;) {
      Arg = Arg->IgnoreParenImpCasts();
      if (const auto *Wrapper = dyn_cast<ExprWithCleanups>(Arg))
        Arg = Wrapper->getSubExpr();
      else if (const auto *Construct = dyn_cast<CXXConstructExpr>(Arg); Construct && Construct->getNumArgs() == 1)
        Arg = Construct->getArg(0);
      else if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Arg))
        Arg = Temporary->getSubExpr();
      else if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(Arg))
        Arg = Bound->getSubExpr();
      else
        return dyn_cast<LambdaExpr>(Arg);
    }
  }
  // The limits of a comparator lambda, decision 0162: captures by copy with no initializer, a call operator that is const, and a body of one
  // `return e;` of a boolean. The return statement, or null. ponytail: `countIf` keeps its own copy of these checks, because it names the limit
  // that each miss breaks, decision 0157. Upgrade: one helper that gives the first missed limit, and `countIf` maps it to its sentence.
  static const ReturnStmt *lambdaReturn(const LambdaExpr *Lambda) {
    const CXXMethodDecl *Operator = Lambda->getCallOperator();
    if (Lambda->getCaptureDefault() == LCD_ByRef || !Operator->isConst())
      return nullptr;
    for (const LambdaCapture &Capture : Lambda->captures())
      if (Capture.getCaptureKind() != LCK_ByCopy || !Capture.capturesVariable() || Lambda->isInitCapture(&Capture))
        return nullptr;
    const auto *Body = dyn_cast_or_null<CompoundStmt>(Operator->getBody());
    const auto *Return = Body && Body->size() == 1 ? dyn_cast<ReturnStmt>(Body->body_front()) : nullptr;
    return Return && Return->getRetValue() && Return->getRetValue()->getType()->isBooleanType() ? Return : nullptr;
  }
  // The type of a comparator parameter, by value or by reference to const, with no qualifier, or null.
  static QualType comparatorParameter(const ParmVarDecl *Parameter) {
    QualType Declared = Parameter->getType();
    if (Declared->isReferenceType()) {
      if (!Declared->isLValueReferenceType() || !Declared->getPointeeType().isConstQualified())
        return QualType();
      Declared = Declared->getPointeeType();
    }
    return Parameter->getIdentifier() ? Declared.getCanonicalType().getUnqualifiedType() : QualType();
  }

  // The kind of a cast of a final class over an interface to one of its interfaces, or null, decision 0166.
  llvm::json::Value upcastKind(const CastExpr *Cast) const {
    const CXXRecordDecl *To = Cast->getType()->getAsCXXRecordDecl();
    const CXXRecordDecl *From = Cast->getSubExpr()->getType()->getAsCXXRecordDecl();
    if (!To || !From || !finalOverInterface(From) || !isInterface(To))
      return nullptr;
    return upcastJson(From, To);
  }
  // The kind `Upcast(D, B)` of a final class over interfaces to one of its interfaces, or null, decisions 0166 and 0168.
  llvm::json::Value upcastJson(const CXXRecordDecl *From, const CXXRecordDecl *To) const {
    if (!From || !To || !finalOverInterface(From) || !isInterface(To))
      return nullptr;
    for (const CXXRecordDecl *B : interfaceBases(From))
      if (B->getCanonicalDecl() == To->getCanonicalDecl()) {
        type(Context.getRecordType(From));
        interfaceEntry(B);
        return tag("Upcast", llvm::json::Array{structKey(From->getDefinition()), structKey(B)});
      }
    return nullptr;
  }
  // The construction `new T(args)` in the body of an instantiated `std::make_unique<T>`, or null.
  static const CXXConstructExpr *constructedByNew(const Stmt *S) {
    if (!S)
      return nullptr;
    if (const auto *New = dyn_cast<CXXNewExpr>(S))
      return New->getConstructExpr();
    for (const Stmt *Child : S->children())
      if (const CXXConstructExpr *Found = constructedByNew(Child))
        return Found;
    return nullptr;
  }
  // `std::move(x)` of a local or a parameter `x` whose type is exactly the `std::unique_ptr<B>` type `Target`: `Move(x, Own(B))`, decision 0171. Null for any other form.
  llvm::json::Value moveOfLocal(const Expr *Moved, QualType Target) const {
    const auto *Call = dyn_cast<CallExpr>(Moved->IgnoreParenImpCasts());
    const FunctionDecl *Callee = Call && Call->getNumArgs() == 1 ? Call->getDirectCallee() : nullptr;
    if (!Callee || !Callee->isInStdNamespace() || !Callee->getDeclName().isIdentifier() || Callee->getName() != "move")
      return nullptr;
    const auto *Ref = dyn_cast<DeclRefExpr>(Call->getArg(0)->IgnoreParenImpCasts());
    const auto *Var = Ref ? dyn_cast<VarDecl>(Ref->getDecl()) : nullptr;
    if (!Var || !Var->hasLocalStorage() || Var->getType()->isReferenceType() || Var->getType().hasQualifiers() ||
        Var->getType().getCanonicalType() != Target.getUnqualifiedType().getCanonicalType())
      return nullptr;
    const QualType Held = ownVecElement(Var->getType());
    if (Held.isNull())
      return nullptr;
    return tag("Move", llvm::json::Array{Var->getNameAsString(), tag("Own", ownScalar(ownElement(Held)))});
  }
  // `std::make_unique<D>(args)` of a final class over an interface, as a `std::unique_ptr<B>` of that interface: `Some(f_D'B(d))` where `d` is the value that the
  // constructor of D gives, or `S_D()` for a class with no field and no constructor, decision 0168. Null for any other form.
  llvm::json::Value makeUniqueUpcast(const CXXConstructExpr *Convert, unsigned Near) const {
    const QualType Into = ownElement(Convert->getType());
    const CXXRecordDecl *Base = Into.isNull() ? nullptr : Into->getAsCXXRecordDecl();
    if (!Base || !isInterface(Base) || Convert->getNumArgs() != 1)
      return nullptr;
    // The argument is the unique_ptr<D> that a call of make_unique gives, behind the temporaries.
    const Expr *Arg = Convert->getArg(0);
    for (;;) {
      Arg = Arg->IgnoreParenImpCasts();
      if (const auto *Wrapper = dyn_cast<ExprWithCleanups>(Arg))
        Arg = Wrapper->getSubExpr();
      else if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Arg))
        Arg = Temporary->getSubExpr();
      else if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(Arg))
        Arg = Bound->getSubExpr();
      else
        break;
    }
    const auto *Make = dyn_cast<CallExpr>(Arg);
    const FunctionDecl *Callee = Make ? Make->getDirectCallee() : nullptr;
    if (!Callee || !Callee->isInStdNamespace() || !Callee->getDeclName().isIdentifier() || Callee->getName() != "make_unique" || !SM.isInSystemHeader(Callee->getLocation()))
      return nullptr;
    const QualType Made = ownElement(Make->getType());
    const CXXRecordDecl *Derived = Made.isNull() ? nullptr : Made->getAsCXXRecordDecl();
    if (!Derived || !plainStruct(Made))
      return nullptr;
    llvm::json::Value Kind = upcastJson(Derived, Base);
    if (Kind.getAsNull())
      return nullptr;
    // The value of D: a class with no field and no constructor of its own is `S_D()`, else the value constructor that make_unique calls.
    llvm::json::Value Built = nullptr;
    const CXXConstructExpr *Constructed = constructedByNew(Callee->getBody());
    if (Derived->field_empty() && !Derived->hasUserDeclaredConstructor() && Make->getNumArgs() == 0) {
      Built = tag("Construct", llvm::json::Array{structKey(Derived->getDefinition()), llvm::json::Array{}});
    } else if (Constructed && valueConstructor(Constructed->getConstructor()) && Constructed->getConstructor()->getNumParams() == Make->getNumArgs()) {
      llvm::json::Array Args;
      for (unsigned I = 0; I < Make->getNumArgs(); ++I) {
        const Expr *A = Make->getArg(I);
        if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(A))
          A = Temporary->getSubExpr();
        // The argument has exactly the type of the parameter, so the construction converts nothing.
        if (A->getType().getUnqualifiedType().getCanonicalType() != Constructed->getConstructor()->getParamDecl(I)->getType().getNonReferenceType().getUnqualifiedType().getCanonicalType())
          return nullptr;
        // An argument `std::move(x)` of a local at a parameter by value of its own unique_ptr type is a move, decision 0171.
        // A parameter by reference binds the xvalue and moves nothing, so that `std::move` keeps its refusal.
        const QualType ParamType = Constructed->getConstructor()->getParamDecl(I)->getType();
        if (llvm::json::Value Moved = ParamType->isReferenceType() ? llvm::json::Value(nullptr) : moveOfLocal(A, ParamType); !Moved.getAsNull())
          Args.push_back(std::move(Moved));
        else
          Args.push_back(expr(A, Near));
      }
      const CXXConstructorDecl *C = Constructed->getConstructor();
      Built = tag("Call", llvm::json::Array{key(C), name(C), std::move(Args), number(line(Convert->getBeginLoc()))});
    }
    if (Built.getAsNull())
      return nullptr;
    return tag("Wrap", tag("Cast", llvm::json::Array{std::move(Kind), std::move(Built)}));
  }

  // The `CountIf` node of a call of `std::count_if` from the library, decision 0149, or null. When the call misses a limit of 0149, `Limit` names the first
  // limit that it misses, in the order of decision 0157. A miss that fits none of them leaves `Limit` empty, and the call stays a call with no model.
  llvm::json::Value countIf(const Expr *E, unsigned Near, std::string &Limit) const {
    const auto *Call = dyn_cast<CallExpr>(E);
    const FunctionDecl *Callee = Call && Call->getStmtClass() == Stmt::CallExprClass ? Call->getDirectCallee() : nullptr;
    if (!Callee || !Callee->isInStdNamespace() || !Callee->getDeclName().isIdentifier() || Callee->getName() != "count_if" || Call->getNumArgs() != 3 ||
        !SM.isInSystemHeader(Callee->getLocation()))
      return nullptr;
    // Both ends come from one sequence parameter.
    const ParmVarDecl *Sequence = nullptr;
    for (const char *Method : {"begin", "end"}) {
      const auto *Member = dyn_cast<CXXMemberCallExpr>(Call->getArg(Method[0] == 'b' ? 0 : 1)->IgnoreParenImpCasts());
      const Expr *Object = Member ? Member->getImplicitObjectArgument() : nullptr;
      const auto *Ref = Object ? dyn_cast<DeclRefExpr>(Object->IgnoreParenImpCasts()) : nullptr;
      const auto *Param = Ref ? dyn_cast<ParmVarDecl>(Ref->getDecl()) : nullptr;
      if (!Member || Member->getNumArgs() != 0 || !Member->getMethodDecl() || !Member->getMethodDecl()->getDeclName().isIdentifier() ||
          Member->getMethodDecl()->getName() != Method || !Param || !(isSeq(Object->getType()) || isMutSeq(Object)) || (Sequence && Sequence != Param)) {
        Limit = "count_if over a range other than v.begin(), v.end() of one sequence parameter";
        return nullptr;
      }
      Sequence = Param;
    }
    // The lambda is written in the call, behind the copies and temporaries that the compiler adds.
    const LambdaExpr *Lambda = lambdaArgument(Call->getArg(2));
    if (!Lambda) {
      Limit = "count_if with a function or a functor in place of a lambda written in the call";
      return nullptr;
    }
    const CXXMethodDecl *Operator = Lambda->getCallOperator();
    // The parameter has the element type, by value or by reference to const. A lambda with another count of parameters misses this limit too.
    QualType Element = seqElement(Sequence->getType());
    // A vector by reference that the function writes is no const sequence, so its element comes from the vector itself, decision 0145.
    if (Element.isNull() && !mutSeq(Sequence->getType()).isNull())
      Element = cast<ClassTemplateSpecializationDecl>(Sequence->getType()->getPointeeType()->getAsCXXRecordDecl())->getTemplateArgs()[0].getAsType();
    const ParmVarDecl *Parameter = Operator->getNumParams() == 1 ? Operator->getParamDecl(0) : nullptr;
    QualType Declared = Parameter ? Parameter->getType() : QualType();
    if (!Declared.isNull() && Declared->isReferenceType()) {
      const bool ConstRef = Declared->isLValueReferenceType() && Declared->getPointeeType().isConstQualified();
      Declared = ConstRef ? Declared->getPointeeType() : QualType();
    }
    if (!Parameter || Declared.isNull() || Element.isNull() || !Parameter->getIdentifier() ||
        Declared.getCanonicalType().getUnqualifiedType() != Element.getCanonicalType().getUnqualifiedType()) {
      Limit = "count_if with a lambda whose parameter is not the element type";
      return nullptr;
    }
    // The captures are by copy, and none has an initializer. A capture by reference, of `this`, and a mutable lambda stay a call with no model.
    if (Lambda->getCaptureDefault() == LCD_ByRef || !Operator->isConst())
      return nullptr;
    for (const LambdaCapture &Capture : Lambda->captures()) {
      if (Capture.capturesVariable() && Lambda->isInitCapture(&Capture)) {
        Limit = "count_if with an init capture in its lambda";
        return nullptr;
      }
      if (Capture.getCaptureKind() != LCK_ByCopy || !Capture.capturesVariable())
        return nullptr;
    }
    // One `return e;` of a boolean.
    const auto *Body = dyn_cast_or_null<CompoundStmt>(Operator->getBody());
    const auto *Return = Body && Body->size() == 1 ? dyn_cast<ReturnStmt>(Body->body_front()) : nullptr;
    if (!Return || !Return->getRetValue()) {
      Limit = "count_if with a lambda whose body is more than one return";
      return nullptr;
    }
    if (!Return->getRetValue()->getType()->isBooleanType())
      return nullptr;
    return tag("CountIf", llvm::json::Array{expr(cast<CXXMemberCallExpr>(Call->getArg(0)->IgnoreParenImpCasts())->getImplicitObjectArgument()->IgnoreParenImpCasts(), Near),
                                            Parameter->getNameAsString(), type(Element), expr(Return->getRetValue(), Near)});
  }

  // The argument `std::move(x)` of a local or a parameter `x` of a plain struct, at a parameter `T&&` of a plain struct, is `x`: the callee writes it back,
  // decision 0179. Any other argument is its expression.
  llvm::json::Value callArg(const FunctionDecl *Callee, unsigned I, const Expr *Arg, unsigned Near) const {
    if (Callee && I < Callee->getNumParams() && Callee->getParamDecl(I)->getType()->isRValueReferenceType() && !mutRef(Callee->getParamDecl(I)->getType()).getAsNull())
      if (const auto *Move = dyn_cast<CallExpr>(Arg->IgnoreParenImpCasts()); Move && Move->getNumArgs() == 1 && Move->getDirectCallee() &&
                                                                              Move->getDirectCallee()->isInStdNamespace() && Move->getDirectCallee()->getDeclName().isIdentifier() &&
                                                                              Move->getDirectCallee()->getName() == "move")
        if (const auto *Ref = dyn_cast<DeclRefExpr>(Move->getArg(0)->IgnoreParenImpCasts());
            Ref && (isa<ParmVarDecl>(Ref->getDecl()) || (isa<VarDecl>(Ref->getDecl()) && cast<VarDecl>(Ref->getDecl())->hasLocalStorage())) && plainStruct(Ref->getType()))
          return expr(Ref, Near);
    return expr(Arg, Near);
  }

  llvm::json::Value expr(const Expr *E, unsigned Near) const {
    if (InConstructorBody && readsObject(E))
      return unknown(E, "a field in the body of a constructor", Near);
    // A temporary that needs a cleanup, such as an optional made from `x + 1`, wraps the expression. The wrapper is not the construct.
    if (const auto *Cleanups = dyn_cast<ExprWithCleanups>(E))
      return expr(Cleanups->getSubExpr(), Near);
    // A temporary of a struct with a destructor is bound for its destructor. The bind is not the value, decision 0178.
    if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(E))
      if (const CXXRecordDecl *RD = plainStruct(Bound->getType()); RD && RD->hasUserDeclaredDestructor())
        return expr(Bound->getSubExpr(), Near);
    // A std::array that a call gives is held in a temporary, which is not the value, decision 0175.
    if (const auto *Held = dyn_cast<MaterializeTemporaryExpr>(E); Held && isStdArray(Held->getType()) && isSeq(Held->getType()))
      return expr(Held->getSubExpr(), Near);
    // A vector that a call gives is held in a temporary, which is not the value, decision 0163.
    if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(E); Bound && !localVec(Bound->getType()).isNull())
      return expr(Bound->getSubExpr(), Near);
    // A `unique_ptr` that a call gives is held in a temporary, which is not the value, decision 0142.
    if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(E); Bound && isOwn(Bound->getType()))
      return expr(Bound->getSubExpr(), Near);
    if (const auto *Held = dyn_cast<MaterializeTemporaryExpr>(E); Held && isOwn(Held->getType()))
      return expr(Held->getSubExpr(), Near);
    // `std::make_unique<D>(args)` of a final class over an interface, as a `std::unique_ptr<B>`, decision 0168.
    if (const auto *Convert = dyn_cast<CXXConstructExpr>(E))
      if (llvm::json::Value Made = makeUniqueUpcast(Convert, Near); !Made.getAsNull())
        return Made;
    // `std::move(x)` of a local or a parameter `x` of exactly the type `std::unique_ptr<B>`, where C++ runs the move constructor of the unique_ptr on it, decision 0171.
    // Any other `std::move` keeps its refusal. So does `std::move` at a parameter `const std::unique_ptr<B>&`, which has no move constructor at all.
    if (const auto *Construct = dyn_cast<CXXConstructExpr>(E); Construct && Construct->getNumArgs() == 1 && Construct->getConstructor()->isMoveConstructor() &&
                                                               !ownVecElement(Construct->getType()).isNull())
      if (llvm::json::Value Moved = moveOfLocal(Construct->getArg(0), Construct->getType()); !Moved.getAsNull())
        return Moved;
    // The move constructor of a unique_ptr over any other `std::move` keeps the refusal of that call, decision 0171.
    if (const auto *Construct = dyn_cast<CXXConstructExpr>(E); Construct && Construct->getNumArgs() == 1 && Construct->getConstructor()->isMoveConstructor() &&
                                                               !ownVecElement(Construct->getType()).isNull())
      if (const auto *Move = dyn_cast<CallExpr>(Construct->getArg(0)->IgnoreParenImpCasts()); Move && Move->getDirectCallee() && Move->getDirectCallee()->isInStdNamespace() &&
                                                                                          Move->getDirectCallee()->getDeclName().isIdentifier() && Move->getDirectCallee()->getName() == "move")
        return expr(Move, Near);
    // The converting constructor of a unique_ptr of an interface from a unique_ptr of another class keeps its argument: the call that gives it is refused, as it was
    // before, decision 0168.
    if (const auto *Convert = dyn_cast<CXXConstructExpr>(E); Convert && Convert->getNumArgs() == 1 && isOwn(Convert->getType()) && isUniquePtr(Convert->getArg(0)->getType()) &&
                                                             Convert->getArg(0)->getType().getUnqualifiedType().getCanonicalType() != Convert->getType().getUnqualifiedType().getCanonicalType())
    {
      const Expr *Inner = Convert->getArg(0);
      for (;;) {
        Inner = Inner->IgnoreParenImpCasts();
        if (const auto *Wrapper = dyn_cast<ExprWithCleanups>(Inner))
          Inner = Wrapper->getSubExpr();
        else if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Inner))
          Inner = Temporary->getSubExpr();
        else if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(Inner))
          Inner = Bound->getSubExpr();
        else
          break;
      }
      // Only a call of the library keeps its own refusal. A unique_ptr of a class that a function of the file gives would be a unique_ptr of the wrong type.
      const auto *Gives = dyn_cast<CallExpr>(Inner);
      if (Gives && Gives->getDirectCallee() && Gives->getDirectCallee()->isInStdNamespace())
        return expr(Inner, Near);
      return unknown(E, "a std::unique_ptr of a class as a std::unique_ptr of its interface", Near);
    }
    // `std::make_unique<T>(x)` of a scalar, with an argument of exactly that type, is a value of `x`, decision 0142.
    if (const auto *Make = dyn_cast<CallExpr>(E); Make && Make->getNumArgs() == 1 && Make->getDirectCallee() && Make->getDirectCallee()->isInStdNamespace() &&
                                                  Make->getDirectCallee()->getDeclName().isIdentifier() && Make->getDirectCallee()->getName() == "make_unique")
      if (const QualType Elem = ownElement(Make->getType()); !Elem.isNull() && scalar(Elem)) {
        const Expr *Arg = Make->getArg(0);
        if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Arg))
          Arg = Temporary->getSubExpr();
        if (Arg->getType().getUnqualifiedType().getCanonicalType() == Elem.getCanonicalType())
          return tag("Wrap", expr(Arg, Near));
      }
    // `p == nullptr` and `p != nullptr` of a `unique_ptr` test for a value, also with the null on the left, decision 0142. Two `unique_ptr`s
    // have no rule. C++20 rewrites `p != nullptr`, `nullptr != p` and `nullptr == p` to a `CXXRewrittenBinaryOperator`, and the test reads its
    // decomposed form. `p == nullptr` is the operator call itself.
    if (const auto *Rewritten = dyn_cast<CXXRewrittenBinaryOperator>(E)) {
      const auto Form = Rewritten->getDecomposedForm();
      if (Form.Opcode == BO_EQ || Form.Opcode == BO_NE) {
        const bool NullLeft = isa<CXXNullPtrLiteralExpr>(Form.LHS->IgnoreParenImpCasts());
        const bool NullRight = isa<CXXNullPtrLiteralExpr>(Form.RHS->IgnoreParenImpCasts());
        const Expr *Pointer = NullLeft ? Form.RHS : Form.LHS;
        if (NullLeft != NullRight && isOwn(Pointer->getType())) {
          const char *Op = Form.Opcode == BO_EQ ? "Eq" : "Ne";
          return tag("Bin", NullRight ? llvm::json::Array{Op, expr(optObject(Pointer), Near), "Nullopt"} : llvm::json::Array{Op, "Nullopt", expr(optObject(Pointer), Near)});
        }
      }
    }
    if (const auto *Test = dyn_cast<CXXOperatorCallExpr>(E); Test && Test->getNumArgs() == 2 && (Test->getOperator() == OO_EqualEqual || Test->getOperator() == OO_ExclaimEqual)) {
      const bool NullLeft = isa<CXXNullPtrLiteralExpr>(Test->getArg(0)->IgnoreParenImpCasts());
      const bool NullRight = isa<CXXNullPtrLiteralExpr>(Test->getArg(1)->IgnoreParenImpCasts());
      const Expr *Pointer = NullLeft ? Test->getArg(1) : Test->getArg(0);
      if (NullLeft != NullRight && isOwn(Pointer->getType())) {
        const char *Op = Test->getOperator() == OO_EqualEqual ? "Eq" : "Ne";
        return tag("Bin", NullRight ? llvm::json::Array{Op, expr(optObject(Pointer), Near), "Nullopt"} : llvm::json::Array{Op, "Nullopt", expr(optObject(Pointer), Near)});
      }
    }
    if (const auto *Flag = dyn_cast<CXXBoolLiteralExpr>(E))
      return tag("Bool", Flag->getValue());
    // A literal of type double is `d / 10^k` of decision 0150, or `m / q` with `q` a power of two, decision 0158. Any other stays unknown.
    if (const auto *Real = dyn_cast<FloatingLiteral>(E); Real && isDouble(Real->getType())) {
      if (llvm::json::Value Form = realForm(Real->getValueAsApproximateDouble()); !Form.getAsNull())
        return Form;
      return unknown(E, "a double literal that the model cannot write exactly", Near);
    }
    if (const auto *Literal = dyn_cast<IntegerLiteral>(E); Literal && Literal->getValue().getActiveBits() <= 64)
      return tag("Lit", llvm::json::Array{number(Literal->getValue().getZExtValue()), type(Literal->getType())});
    if (const auto *Ref = dyn_cast<DeclRefExpr>(E)) {
      const ValueDecl *D = Ref->getDecl();
      if (isa<ParmVarDecl>(D) || (isa<VarDecl>(D) && cast<VarDecl>(D)->hasLocalStorage()) || isGlobal(D))
        return tag("Var", llvm::json::Array{nameOf(D), varType(D)});
      // An enumerator of such an enum is its place among the enumerators, decision 0109.
      if (const auto *Enumerator = dyn_cast<EnumConstantDecl>(D))
        if (const auto *ED = dyn_cast<EnumDecl>(Enumerator->getDeclContext()); ED && plainEnum(Context.getTypeDeclType(ED)) == ED->getDefinition()) {
          enumType(ED);
          return tag("Enumerator", llvm::json::Array{enumKey(ED), number(enumeratorPlace(ED, Enumerator))});
        }
      // An enumerator of a valued enum is its value, a literal of the underlying integer, decision 0175.
      if (const auto *Enumerator = dyn_cast<EnumConstantDecl>(D))
        if (const auto *ED = dyn_cast<EnumDecl>(Enumerator->getDeclContext()); ED && valuedEnum(Context.getTypeDeclType(ED)) == ED->getDefinition())
          return tag("Lit", llvm::json::Array{number(Enumerator->getInitVal().getZExtValue()), valuedType(ED)});
      // A named double constant is its value as a literal is, decision 0158.
      if (const std::optional<double> Real = realConstant(D)) {
        if (llvm::json::Value Form = realForm(*Real); !Form.getAsNull())
          return Form;
        return unknown(E, "a double constant that the model cannot write exactly", Near);
      }
      // A named constant is its value, decision 0106. A negative one is the negation of a literal, as `-5` is.
      if (const std::optional<llvm::APSInt> Value = constant(D)) {
        // The magnitude of a negative value, taken one bit wider so that the minimum of a type does not overflow.
        llvm::APSInt Wide = Value->extend(Value->getBitWidth() + 1);
        if (Value->isNegative())
          Wide = -Wide;
        if (Wide.getActiveBits() <= 64) {
          const llvm::json::Value Own = type(D->getType().getCanonicalType().getUnqualifiedType());
          if (!Value->isNegative())
            return tag("Lit", llvm::json::Array{number(Wide.getZExtValue()), Own});
          // A negative value is computed in int, or in long for int64_t, and converted to its type. The minimum of int and of long is
          // the negation of the maximum, less 1, so that no literal is too large.
          const bool Long = Value->getBitWidth() > 32;
          const char *Computed = Long ? "I64" : "I32";
          const uint64_t Maximum = Long ? INT64_MAX : INT32_MAX;
          llvm::json::Value Negative = Wide.getZExtValue() <= Maximum
                                           ? tag("Neg", tag("Lit", llvm::json::Array{number(Wide.getZExtValue()), Computed}))
                                           : tag("Bin", llvm::json::Array{"Sub", tag("Neg", tag("Lit", llvm::json::Array{number(Maximum), Computed})),
                                                                          tag("Lit", llvm::json::Array{number(1), Computed})});
          if (StringRef(Computed) == Own.getAsString().value_or(""))
            return Negative;
          return tag("Cast", llvm::json::Array{tag("Integral", llvm::json::Array{Computed, Own}), std::move(Negative)});
        }
      }
    }
    // A character is an integer once the compiler has converted it, decision 0106. An ASCII character only: the sign of `char` plays no part.
    if (const auto *Convert = dyn_cast<ImplicitCastExpr>(E); Convert && Convert->getCastKind() == CK_IntegralCast)
      if (const auto *Char = dyn_cast<CharacterLiteral>(Convert->getSubExpr()->IgnoreParens());
          Char && Char->getKind() == CharacterLiteralKind::Ascii && Char->getValue() < 0x80)
        return tag("Lit", llvm::json::Array{number(Char->getValue()), type(Convert->getType())});
    if (const auto *Binary = dyn_cast<BinaryOperator>(E)) {
      const char *Op = nullptr;
      switch (Binary->getOpcode()) {
      case BO_Add: Op = "Add"; break;
      case BO_Sub: Op = "Sub"; break;
      case BO_Mul: Op = "Mul"; break;
      case BO_LT: Op = "Lt"; break;
      case BO_LE: Op = "Le"; break;
      case BO_GT: Op = "Gt"; break;
      case BO_GE: Op = "Ge"; break;
      case BO_EQ: Op = "Eq"; break;
      case BO_NE: Op = "Ne"; break;
      case BO_LAnd: Op = "And"; break;
      case BO_LOr: Op = "Or"; break;
      default: break;
      }
      // A comparison with a pointer operand. Only the test of a pointer to const against nullptr has a rule, decisions 0140 and 0141: two pointers compare
      // addresses, and the model has none. `this` has no rule either.
      if (Binary->isComparisonOp() && (Binary->getLHS()->IgnoreParenImpCasts()->getType()->isPointerType() || Binary->getRHS()->IgnoreParenImpCasts()->getType()->isPointerType())) {
        const bool NullRight = isa<CXXNullPtrLiteralExpr>(Binary->getRHS()->IgnoreParenImpCasts());
        const bool NullLeft = isa<CXXNullPtrLiteralExpr>(Binary->getLHS()->IgnoreParenImpCasts());
        const Expr *Pointer = (NullRight ? Binary->getLHS() : Binary->getRHS())->IgnoreParenImpCasts();
        if ((Binary->getOpcode() == BO_EQ || Binary->getOpcode() == BO_NE) && NullRight != NullLeft && !isa<CXXThisExpr>(Pointer) && !constPointee(Pointer->getType()).isNull())
          return tag("Bin", NullRight ? llvm::json::Array{Op, expr(Pointer, Near), "Nullopt"} : llvm::json::Array{Op, "Nullopt", expr(Pointer, Near)});
        return unknown(E, describe(E), Near);
      }
      // Division and remainder of integers carry the type of their result, decision 0088. Division of a double carries `F64`, and the core refuses it as
      // a rounding, decision 0150. Any other floating point stays unknown.
      if (!Op && (Binary->getOpcode() == BO_Div || Binary->getOpcode() == BO_Rem) && (Binary->getType()->isIntegerType() || isDouble(Binary->getType())))
        return tag("Divide", llvm::json::Array{Binary->getOpcode() == BO_Div ? "Div" : "Rem", expr(Binary->getLHS(), Near), expr(Binary->getRHS(), Near),
                                               type(Binary->getType())});
      // Two values of an enum are compared for equality only, decision 0109.
      if (Op && StringRef(Op) != "Eq" && StringRef(Op) != "Ne" && plainEnum(Binary->getLHS()->getType()))
        return unknown(E, describe(E), Near);
      // `a & b` and `a | b` of integers carry the type of their result, decision 0175. The core refuses a signed result.
      // ponytail: two operands narrower than int promote to int, so `uint8 & uint8` is refused as signed. Upgrade: the operands'
      // unsigned type when both are narrower than int.
      if (!Op && (Binary->getOpcode() == BO_And || Binary->getOpcode() == BO_Or) && Binary->getType()->isIntegerType())
        return tag("Bits", llvm::json::Array{Binary->getOpcode() == BO_And ? "BitAnd" : "BitOr", expr(Binary->getLHS(), Near), expr(Binary->getRHS(), Near), type(Binary->getType())});
      // A right shift carries the type of its result, decision 0106. A left shift has no rule.
      if (!Op && Binary->getOpcode() == BO_Shr)
        return tag("Shr", llvm::json::Array{expr(Binary->getLHS(), Near), expr(Binary->getRHS(), Near), type(Binary->getType())});
      if (!Op)
        return unknown(E, describe(E), Near);
      return tag("Bin", llvm::json::Array{Op, expr(Binary->getLHS(), Near), expr(Binary->getRHS(), Near)});
    }
    if (const auto *Unary = dyn_cast<UnaryOperator>(E)) {
      // `x++`, `x--`, `++x` and `--x` inside an expression, on a target of a write, decision 0177: the name, its type, the direction and the prefix.
      if (Unary->isIncrementDecrementOp())
        if (const auto *Target = dyn_cast<DeclRefExpr>(Unary->getSubExpr()); Target && isTarget(Target->getDecl()))
          return tag("Step", llvm::json::Array{nameOf(Target->getDecl()), varType(Target->getDecl()), Unary->isIncrementOp(), Unary->isPrefix()});
      // `*p` of a pointer to const reads the value behind the pointer, and `&x` of a variable of a scalar or a plain struct is that value as an optional,
      // decision 0140.
      if (Unary->getOpcode() == UO_Deref)
        if (const Expr *Sub = Unary->getSubExpr()->IgnoreParenImpCasts(); !isa<CXXThisExpr>(Sub) && !constPointee(Sub->getType()).isNull())
          return tag("Value", expr(Sub, Near));
      if (Unary->getOpcode() == UO_AddrOf)
        if (const auto *Ref = dyn_cast<DeclRefExpr>(Unary->getSubExpr()->IgnoreParens()); Ref && isVariable(Ref->getDecl()) && mutRef(Ref->getDecl()->getType()).getAsNull() &&
                                                                                          !Ref->getDecl()->getType()->isReferenceType() &&
                                                                                          (scalar(Ref->getType().getUnqualifiedType()) || plainStruct(Ref->getType())))
          return tag("Wrap", expr(Ref, Near));
      if (Unary->getOpcode() == UO_LNot)
        return tag("Not", expr(Unary->getSubExpr(), Near));
      if (Unary->getOpcode() == UO_Minus)
        return tag("Neg", expr(Unary->getSubExpr(), Near));
      return unknown(E, describe(E), Near);
    }
    // `std::chrono::milliseconds{n}` is `n` as an int64, and a copy of one is the value, decision 0175.
    {
      const Expr *Built = E;
      if (const auto *Cast = dyn_cast<CXXFunctionalCastExpr>(E); Cast && Cast->getCastKind() == CK_ConstructorConversion)
        Built = Cast->getSubExpr()->IgnoreParens();
      if (const auto *Construct = dyn_cast<CXXConstructExpr>(Built); Construct && Construct->getNumArgs() == 1 && isMillis(Construct->getType())) {
        const Expr *Arg = Construct->getArg(0);
        if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Arg))
          Arg = Temporary->getSubExpr();
        if (isMillis(Arg->getType()))
          return expr(Arg, Near);
        const QualType From = Arg->getType().getUnqualifiedType();
        const char *Count = scalar(From) ? scalar(From) : smallScalar(From);
        if (Count && StringRef(Count) != "Bool")
          return StringRef(Count) == "I64" ? expr(Arg, Near) : tag("Cast", llvm::json::Array{tag("Integral", llvm::json::Array{type(From), "I64"}), expr(Arg, Near)});
      }
    }
    // `a.count()` of a duration in milliseconds is `a`, and the sum of two is the sum of the counts, decision 0175.
    if (const auto *Count = dyn_cast<CXXMemberCallExpr>(E); Count && Count->getNumArgs() == 0 && Count->getMethodDecl() && Count->getMethodDecl()->getNameAsString() == "count")
      if (const Expr *Object = Count->getImplicitObjectArgument(); Object && isMillis(Object->getType()))
        return expr(Object->IgnoreParenImpCasts(), Near);
    if (const auto *Sum = dyn_cast<CXXOperatorCallExpr>(E); Sum && Sum->getOperator() == OO_Plus && Sum->getNumArgs() == 2 && isMillis(Sum->getType()) &&
                                                             isMillis(Sum->getArg(0)->getType()) && isMillis(Sum->getArg(1)->getType()))
      return tag("Bin", llvm::json::Array{"Add", expr(Sum->getArg(0)->IgnoreParenImpCasts(), Near), expr(Sum->getArg(1)->IgnoreParenImpCasts(), Near)});
    // A use of a free operator function of the file is a call of it, decision 0175. A member operator and a library operator keep their refusal.
    if (const auto *Use = dyn_cast<CXXOperatorCallExpr>(E); Use && Use->getDirectCallee() && !isa<CXXMethodDecl>(Use->getDirectCallee()) &&
                                                             freeOperator(Use->getOperator()) && !SM.isInSystemHeader(Use->getDirectCallee()->getLocation())) {
      llvm::json::Array Args;
      for (const Expr *Arg : Use->arguments())
        Args.push_back(expr(Arg, line(E->getBeginLoc())));
      return tag("Call", llvm::json::Array{key(Use->getDirectCallee()), name(Use->getDirectCallee()), std::move(Args), number(line(E->getBeginLoc()))});
    }
    // `{a, b, c}` of a std::array is the list of its values, decision 0175. The braces of the member array inside are looked through.
    if (const auto *List = dyn_cast<InitListExpr>(E); List && isStdArray(List->getType()) && isSeq(List->getType())) {
      const InitListExpr *Values = List;
      if (List->getNumInits() == 1)
        if (const auto *Inner = dyn_cast<InitListExpr>(List->getInit(0)); Inner && Inner->getType()->isArrayType())
          Values = Inner;
      llvm::json::Array Items;
      for (const Expr *Init : Values->inits())
        Items.push_back(expr(Init, Near));
      return tag("List", std::move(Items));
    }
    // A call of a value constructor, `S s(a)`, `S s{a}`, `S(a)` and `return S(a)`, is a call of it, decision 0094. The functional cast of
    // one argument wraps the construction, and the call stands for both.
    {
      const Expr *Built = E;
      if (const auto *Cast = dyn_cast<CXXFunctionalCastExpr>(E); Cast && Cast->getCastKind() == CK_ConstructorConversion)
        Built = Cast->getSubExpr()->IgnoreParens();
      if (const auto *Construct = dyn_cast<CXXConstructExpr>(Built); Construct && valueConstructor(Construct->getConstructor())) {
        llvm::json::Array Args;
        for (unsigned I = 0; I < Construct->getNumArgs(); ++I)
          Args.push_back(callArg(Construct->getConstructor(), I, Construct->getArg(I), line(E->getBeginLoc())));
        return tag("Call", llvm::json::Array{key(Construct->getConstructor()), name(Construct->getConstructor()), std::move(Args), number(line(E->getBeginLoc()))});
      }
    }
    if (const auto *Cast = dyn_cast<CastExpr>(E)) {
      // `nullptr` as an argument for a pointer to const is no value, decision 0140.
      if (Cast->getCastKind() == CK_NullToPointer && isa<CXXNullPtrLiteralExpr>(Cast->getSubExpr()->IgnoreParens()))
        return "Nullopt";
      // A final class at a reference of its interface that is not const has no rule: the model has no way back from a value of the interface, decision 0169.
      if (Cast->getCastKind() == CK_DerivedToBase && !Cast->getType().isConstQualified() && Cast->getValueKind() == VK_LValue && !upcastKind(Cast).getAsNull())
        return unknown(E, "a class as a reference to its interface", Near);
      llvm::json::Value Kind = Cast->getCastKind() == CK_LValueToRValue ? llvm::json::Value("Read")
                               : Cast->getCastKind() == CK_NoOp         ? llvm::json::Value("NoOp")
                               : Cast->getCastKind() == CK_ConstructorConversion ? llvm::json::Value("Construct")
                               : Cast->getCastKind() == CK_IntegralCast && !plainEnum(Cast->getSubExpr()->getType()) && !plainEnum(Cast->getType()) ? tag("Integral", llvm::json::Array{type(Cast->getSubExpr()->getType()), type(Cast->getType())})
                               // An integer scalar to a double, decision 0159. A bool and an enum are no integer here, and a double to an integer stays `Other`.
                               // An enum is no scalar here.
                               : Cast->getCastKind() == CK_IntegralToFloating && isDouble(Cast->getType()) &&
                                     (scalar(Cast->getSubExpr()->getType().getUnqualifiedType()) || smallScalar(Cast->getSubExpr()->getType().getUnqualifiedType())) &&
                                     !Cast->getSubExpr()->getType()->isBooleanType()
                                   ? tag("Integral", llvm::json::Array{type(Cast->getSubExpr()->getType().getUnqualifiedType()), type(Cast->getType())})
                               // A final class over an interface to that interface, decision 0166. Any other derived-to-base cast stays `Other`.
                               : Cast->getCastKind() == CK_DerivedToBase && !upcastKind(Cast).getAsNull() ? upcastKind(Cast)
                                                                        : tag("Other", std::string(Cast->getStmtClassName()) + " " + Cast->getCastKindName());
      return tag("Cast", llvm::json::Array{std::move(Kind), expr(Cast->getSubExpr(), Near)});
    }
    if (const auto *Paren = dyn_cast<ParenExpr>(E))
      return tag("Paren", expr(Paren->getSubExpr(), Near));
    // `c ? a : b`, decision 0098. The GNU form `c ?: b` stays unknown.
    if (const auto *Choice = dyn_cast<ConditionalOperator>(E))
      return tag("Cond", llvm::json::Array{expr(Choice->getCond(), Near), expr(Choice->getTrueExpr(), Near), expr(Choice->getFalseExpr(), Near)});
    // A local vector made from a sequence in scope is a copy, decision 0160: a parameter or another local vector. A copy from any other expression, a call or
    // a list, stays unknown, and the core refuses the local.
    if (const auto *Construct = dyn_cast<CXXConstructExpr>(E); Construct && Construct->getNumArgs() == 1 && !localVec(Construct->getType()).isNull()) {
      const auto *Source = dyn_cast<DeclRefExpr>(Construct->getArg(0)->IgnoreParenImpCasts());
      const auto *Named = Source ? dyn_cast<VarDecl>(Source->getDecl()) : nullptr;
      if (Named && (isSeq(Source->getType()) || isMutSeq(Source)) && (isa<ParmVarDecl>(Named) || Named->hasLocalStorage()))
      {
        // The core judges a copy of a sequence by two `Seq` types. A vector the function writes is a dynamic sequence of its element.
        const QualType Written = isa<ParmVarDecl>(Named) ? mutSeq(Named->getType()) : localVec(Named->getType());
        llvm::json::Value From = !Written.isNull() ? tag("Seq", llvm::json::Array{elementType(Written), nullptr}) : type(Source->getType());
        return tag("Copy", llvm::json::Array{expr(Source, Near), std::move(From), tag("Seq", llvm::json::Array{elementType(localVec(Construct->getType())), nullptr})});
      }
    }
    // `std::vector<T> v;` with no initial value is the empty sequence, decision 0170.
    if (const auto *Default = dyn_cast<CXXConstructExpr>(E); Default && Default->getNumArgs() == 0 && Default->getConstructor()->isDefaultConstructor() && !localVec(Default->getType()).isNull())
      return "EmptyVec";
    // `const D d;` of a plain struct with no field and no constructor of its own is the value `S_D()`, decision 0166.
    if (const auto *Default = dyn_cast<CXXConstructExpr>(E); Default && Default->getNumArgs() == 0 && Default->getConstructor()->isDefaultConstructor()) {
      const CXXRecordDecl *RD = plainStruct(Default->getType());
      if (RD && RD->field_empty() && !RD->hasUserDeclaredConstructor())
        return tag("Construct", llvm::json::Array{structKey(RD), llvm::json::Array{}});
    }
    // A copy of a struct with a destructor is the name, so the core refuses it as a copy, decision 0178.
    if (const auto *Construct = dyn_cast<CXXConstructExpr>(E); Construct && Construct->getNumArgs() == 1 && plainStruct(Construct->getType()) &&
                                                               plainStruct(Construct->getArg(0)->getType()) && plainStruct(Construct->getType())->hasUserDeclaredDestructor())
      return expr(Construct->getArg(0), Near);
    // A copy or a move by a constructor that the file writes runs code that the model cannot see, decision 0179. One that the model can call was a call above.
    if (const auto *Construct = dyn_cast<CXXConstructExpr>(E); Construct && Construct->getNumArgs() == 1 && plainStruct(Construct->getType()) &&
                                                               Construct->getConstructor()->isCopyOrMoveConstructor() && Construct->getConstructor()->isUserProvided())
      return unknown(E, "a copy or a move by a constructor that the model cannot call", Near);
    // A sequence made from one sequence, decision 0070, or a struct made from one struct, decision 0073. The core judges the two types.
    if (const auto *Construct = dyn_cast<CXXConstructExpr>(E);
        Construct && Construct->getNumArgs() == 1 &&
        ((isSeq(Construct->getType()) && isSeq(Construct->getArg(0)->getType())) ||
         (plainStruct(Construct->getType()) && plainStruct(Construct->getArg(0)->getType()))))
      return tag("Copy", llvm::json::Array{expr(Construct->getArg(0), Near), type(Construct->getArg(0)->getType()), type(Construct->getType())});
    // An optional of a scalar, decision 0075: `std::nullopt`, a value that the compiler turns into one, and a copy of one. The core
    // judges the two types of the copy. A construction from any other argument stays unknown.
    if (const auto *Construct = dyn_cast<CXXConstructExpr>(E); Construct && Construct->getNumArgs() == 1 && isOpt(Construct->getType())) {
      const Expr *Arg = Construct->getArg(0);
      const QualType From = Arg->getType().getNonReferenceType().getUnqualifiedType().getCanonicalType();
      const CXXRecordDecl *Tag = From->getAsCXXRecordDecl();
      if (Tag && Tag->isInStdNamespace() && Tag->getName() == "nullopt_t") {
        // Only the variable `std::nullopt` itself is `None`, through its implicit casts, parentheses and copies. Any other expression
        // of the type may hold a call or a read, so it stays an unknown construct.
        const Expr *Name = Arg->IgnoreParenImpCasts();
        while (const auto *Copy = dyn_cast<CXXConstructExpr>(Name)) {
          if (Copy->getNumArgs() != 1)
            break;
          Name = Copy->getArg(0)->IgnoreParenImpCasts();
        }
        if (const auto *Ref = dyn_cast<DeclRefExpr>(Name); Ref && isa<VarDecl>(Ref->getDecl()) && Ref->getDecl()->isInStdNamespace() &&
                                                           Ref->getDecl()->getName() == "nullopt")
          return "Nullopt";
        return unknown(E, E->getStmtClassName(), Near);
      }
      if (isOpt(Arg->getType()))
        return tag("Copy", llvm::json::Array{expr(Arg, Near), type(Arg->getType()), type(Construct->getType())});
      if (From == optType(Construct->getType()).getCanonicalType()) {
        // A computed value, `x + 1`, is held in a temporary for the reference parameter of the constructor. The temporary is not the value.
        if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Arg))
          Arg = Temporary->getSubExpr();
        return tag("Wrap", expr(Arg, Near));
      }
    }
    // `o.has_value()` and `o.value()`.
    if (const auto *Member = dyn_cast<CXXMemberCallExpr>(E); Member && Member->getNumArgs() == 0 && Member->getMethodDecl())
      if (const Expr *Object = Member->getImplicitObjectArgument(); Object && isOpt(Object->getType())) {
        const std::string Method = Member->getMethodDecl()->getNameAsString();
        if (Method == "has_value")
          return tag("HasValue", expr(optObject(Object), Near));
        if (Method == "value")
          return tag("Value", expr(optObject(Object), Near));
      }
    // `*o`, and `*p` of a `unique_ptr`, decision 0142.
    if (const auto *Operator = dyn_cast<CXXOperatorCallExpr>(E); Operator && Operator->getOperator() == OO_Star && Operator->getNumArgs() == 1 &&
                                                                  (isOpt(Operator->getArg(0)->getType()) || isOwn(Operator->getArg(0)->getType())))
      return tag("Value", expr(optObject(Operator->getArg(0)), Near));
    if (const auto *List = dyn_cast<InitListExpr>(E); List && List->getNumInits() == 1 && List->getType()->isScalarType())
      return tag("Brace", expr(List->getInit(0), Near));
    // A braced value of a plain struct. A field that the list leaves out is an `ImplicitValueInitExpr`, which stays unknown.
    if (const auto *List = dyn_cast<InitListExpr>(E); List && plainStruct(List->getType())) {
      llvm::json::Array Args;
      for (const Expr *Init : List->inits())
        Args.push_back(expr(Init, Near));
      type(List->getType());  // writes the struct
      return tag("Construct", llvm::json::Array{structKey(plainStruct(List->getType())), std::move(Args)});
    }
    // The object of a const member function, decision 0089.
    if (const auto *This = dyn_cast<CXXThisExpr>(E); This && plainStruct(This->getType()->getPointeeType()))
      return tag("Var", llvm::json::Array{"this", thisType(This->getType()->getPointeeType()->getAsCXXRecordDecl(), !This->getType()->getPointeeType().isConstQualified())});
    // `p->f` on a pointer to const of a plain struct reads the field of its value, decision 0140.
    if (const auto *Member = dyn_cast<MemberExpr>(E); Member && Member->isArrow())
      if (const Expr *Base = Member->getBase()->IgnoreParenImpCasts(); !isa<CXXThisExpr>(Base) && !constPointee(Base->getType()).isNull())
        if (const auto *Field = dyn_cast<FieldDecl>(Member->getMemberDecl()); Field && plainStruct(Context.getRecordType(Field->getParent())))
          return tag("Field", llvm::json::Array{tag("Value", expr(Base, Near)), Field->getNameAsString()});
    // `o->f` on an optional of a plain struct reads the field of its value, decision 0137. `p->f` on a `unique_ptr`, decision 0142.
    if (const auto *Member = dyn_cast<MemberExpr>(E); Member && Member->isArrow())
      if (const auto *Arrow = dyn_cast<CXXOperatorCallExpr>(Member->getBase()->IgnoreParenImpCasts());
          Arrow && Arrow->getOperator() == OO_Arrow && Arrow->getNumArgs() == 1 && (isOpt(Arrow->getArg(0)->getType()) || isOwn(Arrow->getArg(0)->getType())))
        if (const auto *Field = dyn_cast<FieldDecl>(Member->getMemberDecl()); Field && plainStruct(Context.getRecordType(Field->getParent())))
          return tag("Field", llvm::json::Array{tag("Value", expr(optObject(Arrow->getArg(0)), Near)), Field->getNameAsString()});
    // A read of a field of a plain struct, also through `this`.
    if (const auto *Member = dyn_cast<MemberExpr>(E); Member && (!Member->isArrow() || isa<CXXThisExpr>(Member->getBase()->IgnoreParenImpCasts())))
      if (const auto *Field = dyn_cast<FieldDecl>(Member->getMemberDecl()); Field && plainStruct(Context.getRecordType(Field->getParent())))
        return tag("Field", llvm::json::Array{expr(Member->getBase()->IgnoreParenImpCasts(), Near), Field->getNameAsString()});
    // `v.size()` and `v[i]` of a read-only sequence.
    if (const auto *Member = dyn_cast<CXXMemberCallExpr>(E); Member && Member->getNumArgs() == 0 && Member->getMethodDecl() && Member->getMethodDecl()->getNameAsString() == "size")
      if (const Expr *Object = Member->getImplicitObjectArgument(); Object && (isSeq(Object->getType()) || isMutSeq(Object)))
        return tag("Size", expr(Object, Near));
    // `v.empty()`, and `s.subspan(k)` with no explicit second argument, decision 0078. `subspan(k, n)` and `first(n)` stay unknown.
    if (const auto *Member = dyn_cast<CXXMemberCallExpr>(E); Member && Member->getNumArgs() == 0 && Member->getMethodDecl() && Member->getMethodDecl()->getNameAsString() == "empty")
      if (const Expr *Object = Member->getImplicitObjectArgument(); Object && isSeq(Object->getType()))
        return tag("Empty", expr(Object, Near));
    if (const auto *Member = dyn_cast<CXXMemberCallExpr>(E); Member && Member->getNumArgs() == 2 && isa<CXXDefaultArgExpr>(Member->getArg(1)) &&
                                                             Member->getMethodDecl() && Member->getMethodDecl()->getNameAsString() == "subspan")
      if (const Expr *Object = Member->getImplicitObjectArgument(); Object && isSeq(Object->getType()))
        return tag("Subspan", llvm::json::Array{expr(Object, Near), expr(Member->getArg(0), Near)});
    if (const auto *Operator = dyn_cast<CXXOperatorCallExpr>(E); Operator && Operator->getOperator() == OO_Subscript && Operator->getNumArgs() == 2 &&
                                                                  (isSeq(Operator->getArg(0)->getType()) || isMutSeq(Operator->getArg(0))))
      return tag("Index", llvm::json::Array{expr(Operator->getArg(0), Near), expr(Operator->getArg(1), Near)});
    // `v.at(i)` of a read-only sequence is `v[i]`, decision 0139. The prover proves the index in range, so `at` never throws.
    if (const auto *Member = dyn_cast<CXXMemberCallExpr>(E); Member && Member->getNumArgs() == 1 && Member->getMethodDecl() && Member->getMethodDecl()->getNameAsString() == "at")
      if (const Expr *Object = Member->getImplicitObjectArgument(); Object && isSeq(Object->getType()))
        return tag("Index", llvm::json::Array{expr(Object, Near), expr(Member->getArg(0), Near)});
    // `p->f(a)` on a unique_ptr of an interface is a call of the function of the interface on the value of `p`, decision 0168.
    if (const auto *Call = dyn_cast<CXXMemberCallExpr>(E); Call && Call->getDirectCallee() && ifaceMethod(Call->getDirectCallee()))
      if (const auto *Arrow = dyn_cast<CXXOperatorCallExpr>(Call->getImplicitObjectArgument()->IgnoreParenImpCasts());
          Arrow && Arrow->getOperator() == OO_Arrow && Arrow->getNumArgs() == 1 && isOwn(Arrow->getArg(0)->getType())) {
        const auto *Callee = dyn_cast<MemberExpr>(Call->getCallee()->IgnoreParens());
        if (Callee && Callee->hasQualifier())
          return unknown(E, "a qualified call of a virtual function", Near);
        // A call that writes the object names the variable, with no cast, so the core finds the unique_ptr that takes the new value, decision 0169.
        // So does the element of a vector of unique_ptr, `v[i]->f(a)`, decision 0170.
        const Expr *Bare = Arrow->getArg(0)->IgnoreParenImpCasts();
        const auto *Element = dyn_cast<CXXOperatorCallExpr>(Bare);
        const Expr *Pointer = Call->getMethodDecl()->isConst() || !(isa<DeclRefExpr>(Bare) || (Element && Element->getOperator() == OO_Subscript)) ? optObject(Arrow->getArg(0)) : Bare;
        llvm::json::Array Args{tag("Value", expr(Pointer, line(E->getBeginLoc())))};
        for (const Expr *Arg : Call->arguments())
          Args.push_back(expr(Arg, line(E->getBeginLoc())));
        return tag("Call", llvm::json::Array{key(Call->getDirectCallee()), name(Call->getDirectCallee()), std::move(Args), number(line(E->getBeginLoc()))});
      }
    // A call of a member function, `o.f(a)` or `f(a)` in a method, is a call of `f` with the object first, decisions 0089 and 0096.
    if (const auto *Call = dyn_cast<CXXMemberCallExpr>(E); Call && Call->getDirectCallee() && member(Call->getDirectCallee())) {
      const Expr *Object = Call->getImplicitObjectArgument()->IgnoreParenImpCasts();
      const auto *Callee = dyn_cast<MemberExpr>(Call->getCallee()->IgnoreParens());
      // A call of a virtual function with the name of its class runs that function, not an override, decision 0165.
      if (Callee && Callee->hasQualifier() && Call->getMethodDecl() && Call->getMethodDecl()->isVirtual())
        return unknown(E, "a qualified call of a virtual function", Near);
      if (Callee && (!Callee->isArrow() || isa<CXXThisExpr>(Object))) {
        llvm::json::Array Args{expr(Object, line(E->getBeginLoc()))};
        for (unsigned I = 0; I < Call->getNumArgs(); ++I)
          Args.push_back(callArg(Call->getDirectCallee(), I, Call->getArg(I), line(E->getBeginLoc())));
        return tag("Call", llvm::json::Array{key(Call->getDirectCallee()), name(Call->getDirectCallee()), std::move(Args), number(line(E->getBeginLoc()))});
      }
    }
    // A call of an object, `c(x)`, is a call of its `operator()` with the object first, decision 0098.
    if (const auto *Call = dyn_cast<CXXOperatorCallExpr>(E); Call && Call->getOperator() == OO_Call && Call->getNumArgs() >= 1 && Call->getDirectCallee() &&
                                                             member(Call->getDirectCallee())) {
      llvm::json::Array Args{expr(Call->getArg(0)->IgnoreParenImpCasts(), line(E->getBeginLoc()))};
      for (unsigned I = 1; I < Call->getNumArgs(); ++I)
        Args.push_back(expr(Call->getArg(I), line(E->getBeginLoc())));
      return tag("Call", llvm::json::Array{key(Call->getDirectCallee()), name(Call->getDirectCallee()), std::move(Args), number(line(E->getBeginLoc()))});
    }
    // `std::count_if(v.begin(), v.end(), [captures](T x) { return e; })` over a sequence parameter, decision 0149. The captures are by copy and the
    // body is one `return`. Anything else stays a call, which has no model, and is refused.
    std::string Limit;
    if (const llvm::json::Value Counted = countIf(E, Near, Limit); !Counted.getAsNull())
      return Counted;
    // A count_if that misses a limit names it, decision 0157.
    if (!Limit.empty())
      return unknown(E, Limit, Near);
    // Only a plain call by name. A member call, an operator call and the rest of the call classes stay unknown.
    if (E->getStmtClass() == Stmt::CallExprClass)
      if (const FunctionDecl *Callee = cast<CallExpr>(E)->getDirectCallee()) {
        llvm::json::Array Args;
        for (unsigned I = 0; I < cast<CallExpr>(E)->getNumArgs(); ++I) {
          const Expr *Arg = cast<CallExpr>(E)->getArg(I);
          // A class at a reference of its interface that is not const stands for the whole call, because the core would refuse the write-back first, decision 0169.
          if (const auto *Up = dyn_cast<ImplicitCastExpr>(Arg->IgnoreParens()); Up && Up->getCastKind() == CK_DerivedToBase && !Up->getType().isConstQualified() &&
                                                                              Up->getValueKind() == VK_LValue && !upcastKind(Up).getAsNull())
            return unknown(E, "a class as a reference to its interface", Near);
          Args.push_back(callArg(Callee, I, Arg, line(E->getBeginLoc())));
        }
        return tag("Call", llvm::json::Array{key(Callee), name(Callee), std::move(Args), number(line(E->getBeginLoc()))});
      }
    return unknown(E, E->getStmtClassName(), Near);
  }
};

// Everything in view is accounted for. Each function that a non-system file defines is written, and each `//@` line of such a file that
// no function claimed is written as `{"orphan": line, "file": name}`. A deleted function runs nothing, so it is not written, and it
// claims no line.
// ponytail: the orphan scan reads the text, not the tokens. A line that holds `//@` anywhere is an orphan when nothing claimed it, and
// only a line that starts with `//@` can be claimed. So a `//@` after code, in a block comment or in a raw string is an orphan too,
// which only refuses more. Upgrade: the lexer's comment tokens.
class TreeCheck : public ClangTidyCheck {
public:
  TreeCheck(StringRef Name, ClangTidyContext *Context) : ClangTidyCheck(Name, Context), Output(Options.get("Output", "")) {}
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(
        functionDecl(unless(isImplicit()), unless(isTemplateInstantiation()), unless(isExpansionInSystemHeader())).bind("fn"), this);
    Finder->addMatcher(varDecl(isConstexpr(), unless(isExpansionInSystemHeader())).bind("constant"), this);
    Finder->addMatcher(varDecl(hasGlobalStorage(), unless(isConstexpr()), unless(isExpansionInSystemHeader())).bind("global"), this);
    Finder->addMatcher(enumDecl(isDefinition(), unless(isExpansionInSystemHeader())).bind("enum"), this);
    Finder->addMatcher(cxxRecordDecl(isDefinition(), unless(isImplicit()), unless(isExpansionInSystemHeader())).bind("class"), this);
    Finder->addMatcher(translationUnitDecl(), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    Context = Result.Context;
    // The named constants of the file, decision 0106. A contract reads them by name.
    if (const auto *Var = Result.Nodes.getNodeAs<VarDecl>("constant")) {
      llvm::json::Value Line = TreeWriter(*Context, Claimed, Structs).constantLine(Var);
      if (Line.kind() != llvm::json::Value::Null)
        append(Line);
      return;
    }
    // The mutable globals and static data members of the file, in the order of their definitions, decision 0173.
    if (const auto *Var = Result.Nodes.getNodeAs<VarDecl>("global")) {
      llvm::json::Value Line = TreeWriter(*Context, Claimed, Structs).globalLine(Var);
      if (Line.kind() != llvm::json::Value::Null)
        append(Line);
      return;
    }
    // Each enum class of the file is written, whether or not a type names it, decision 0114.
    if (const auto *ED = Result.Nodes.getNodeAs<EnumDecl>("enum")) {
      TreeWriter(*Context, Claimed, Structs).writeEnum(ED);
      return;
    }
    // A class over interfaces is written in the table of structs for its line, decision 0165.
    if (const auto *RD = Result.Nodes.getNodeAs<CXXRecordDecl>("class")) {
      TreeWriter(*Context, Claimed, Structs).classEntry(RD);
      TreeWriter(*Context, Claimed, Structs).staticEntry(RD);
      TreeWriter(*Context, Claimed, Structs).holderEntry(RD);
      return;
    }
    const auto *FD = Result.Nodes.getNodeAs<FunctionDecl>("fn");
    // A defaulted destructor has no contract and no body, so it is no member of the model, decision 0178.
    if (!FD || FD->isDeleted() || (isa<CXXDestructorDecl>(FD) && FD->isDefaulted()))
      return;
    // The call operator of a lambda is no function of its own, decision 0149. The call that takes the lambda reads its body, or is refused.
    if (const auto *Method = dyn_cast<CXXMethodDecl>(FD); Method && Method->getParent()->isLambda())
      return;
    const Contract C = contractOf(Context->getSourceManager(), FD);
    for (const Contract::Line &L : C.Lines)
      Claimed.insert({L.File, L.Number});
    // The member functions of a class over an interface that is not final, and the defaulted destructor of an interface, are left out, decision 0165.
    if (TreeWriter(*Context, Claimed, Structs).leftOut(FD))
      return;
    // A trusted function with no definition here is written once, at its first declaration. Its contract lines come from all of them.
    // ponytail: a trusted template is not written. A trusted constructor with no body here is written and refused as CXXConstructorDecl, and
    // one with a body is refused by valueConstructor unless its body is empty and it gives each field a value. Upgrade: their signatures.
    if (FD->isThisDeclarationADefinition() || (TreeWriter(*Context, Claimed, Structs).ifaceMethod(FD) && !FD->getDefinition()) ||
        (!FD->getDefinition() && FD == FD->getCanonicalDecl() && !FD->isTemplated() && trustedReason(FD)))
      append(TreeWriter(*Context, Claimed, Structs).function(FD, C));
  }
  void onEndOfTranslationUnit() override {
    if (!Context)
      return;
    const SourceManager &SM = Context->getSourceManager();
    for (const auto &[Key, Line] : Structs)
      append(Line);
    for (unsigned I = 0; I < SM.local_sloc_entry_size(); ++I) {
      const SrcMgr::SLocEntry &Entry = SM.getLocalSLocEntry(I);
      if (!Entry.isFile())
        continue;
      const SourceLocation Start = SourceLocation::getFromRawEncoding(Entry.getOffset());
      const FileID ID = SM.getFileID(Start);
      // The compiler's own buffers, such as the predefined macros, are no file.
      if (!SM.getFileEntryForID(ID) || SM.isInSystemHeader(Start))
        continue;
      unsigned Number = 0;
      for (StringRef Rest = SM.getBufferData(ID); !Rest.empty();) {
        const auto [Line, Tail] = Rest.split('\n');
        ++Number;
        Rest = Tail;
        if (Line.contains("//@") && !Claimed.count({ID.getHashValue(), Number}))
          append(llvm::json::Object{{"orphan", static_cast<int64_t>(Number)}, {"file", SM.getFilename(Start).str()}, {"word", orphanWord(Line)}});
      }
    }
  }

private:
  // The word of a line that starts with `//@`, else empty. The translator says more for an assert or apply line, decision 0099.
  static std::string orphanWord(StringRef Line) {
    Line = Line.trim();
    if (!Line.consume_front("//@"))
      return "";
    Line = Line.ltrim();
    return Line.substr(0, Line.find_first_of(" \t\f\v\r")).str();
  }

  std::string Output;
  ASTContext *Context = nullptr;
  std::set<std::pair<unsigned, unsigned>> Claimed;
  std::map<std::string, llvm::json::Value> Structs;  // each plain struct that a function names, by key

  void append(const llvm::json::Value &V) {
    std::error_code EC;
    llvm::raw_fd_ostream OS(Output, EC, llvm::sys::fs::OF_Append | llvm::sys::fs::OF_Text);
    if (EC) {
      configurationDiag("cplusp-tree cannot write %0: %1") << Output << EC.message();
      return;
    }
    OS << llvm::formatv("{0}", V) << "\n";
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
    Factories.registerCheck<RawCopyCheck>("cplusp-raw-copy");
    Factories.registerCheck<LineDirectiveCheck>("cplusp-line-directive");
    Factories.registerCheck<PragmaCheck>("cplusp-pragma");
    Factories.registerCheck<MarkersCheck>("cplusp-markers");
    Factories.registerCheck<IndirectCallCheck>("cplusp-indirect-call");
    Factories.registerCheck<TreeCheck>("cplusp-tree");
  }
};

} // namespace

static clang::tidy::ClangTidyModuleRegistry::Add<CplusPModule> X("cplusp-module", "Adds the checks of cplusp.");

// Forces a linker to keep this module when it is linked in. A loaded plugin does not need it.
volatile int CplusPModuleAnchorSource = 0;
