// The clang-tidy plugin of cplusp. See docs/policy.md.
//
// One generic check, driven by the policy file.
// The gate writes each `matcher` entry of a rule as an option of the check, named `{rule_id}/{n}`.
// The check compiles the pattern and reports every match with the rule id as its message.
// The Rust side turns the rule id into the message for the bot.
//
// Five hand-written checks, for the rules that a pattern cannot say. The gate maps a finding to its rule by
// the name of the check, so their messages are short and plain. The sample pair of each rule is the evidence.

#include "ClangTidyCheck.h"
#include "ClangTidyModule.h"
#include "ClangTidyModuleRegistry.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/Dynamic/Diagnostics.h"
#include "clang/ASTMatchers/Dynamic/Parser.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringSet.h"

#include <optional>
#include <string>

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
AST_MATCHER(Decl, isInStd) {
  for (const DeclContext *Context = Node.getDeclContext(); Context; Context = Context->getParent())
    if (Context->isStdNamespace())
      return true;
  return false;
}

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

bool isImpureOperator(const FunctionDecl *Function) {
  switch (Function->getOverloadedOperator()) {
  case OO_Equal: case OO_PlusEqual: case OO_MinusEqual: case OO_StarEqual: case OO_SlashEqual: case OO_PercentEqual:
  case OO_AmpEqual: case OO_PipeEqual: case OO_CaretEqual: case OO_LessLessEqual: case OO_GreaterGreaterEqual:
  case OO_PlusPlus: case OO_MinusMinus:
    return true;
  default:
    break;
  }
  // A static member has no object, so it is judged like a free function.
  const auto *Method = dyn_cast<CXXMethodDecl>(Function);
  if (Method && !Method->isStatic())
    return !Method->isConst();
  return llvm::any_of(Function->parameters(), [](const ParmVarDecl *Parameter) {
    QualType Type = Parameter->getType();
    return (Type->isReferenceType() || Type->isPointerType()) && !Type->getPointeeType().isConstQualified();
  });
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

// cplusp-lambda-limits: a lambda that is no direct argument of a std call, or that captures by reference or `this`.
class LambdaLimitsCheck : public SpelledCheck {
public:
  using SpelledCheck::SpelledCheck;
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(lambdaExpr(anyOf(unless(hasParent(stdCall())), capturesByReferenceOrThis())).bind("lambda"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    diag(Result.Nodes.getNodeAs<LambdaExpr>("lambda")->getBeginLoc(), "lambda is outside its limits");
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
  }
};

} // namespace

static clang::tidy::ClangTidyModuleRegistry::Add<CplusPModule> X("cplusp-module", "Adds the checks of cplusp.");

// Forces a linker to keep this module when it is linked in. A loaded plugin does not need it.
volatile int CplusPModuleAnchorSource = 0;
