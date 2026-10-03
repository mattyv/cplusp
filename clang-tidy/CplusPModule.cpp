// The clang-tidy plugin of cplusp. One generic check, driven by the policy file.
// The gate writes each `matcher` entry of a rule as an option of the check, named `{rule_id}/{n}`.
// The check compiles the pattern and reports every match with the rule id as its message.
// The Rust side turns the rule id into the message for the bot. See docs/policy.md.

#include "ClangTidyCheck.h"
#include "ClangTidyModule.h"
#include "ClangTidyModuleRegistry.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/Dynamic/Diagnostics.h"
#include "clang/ASTMatchers/Dynamic/Parser.h"
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

class CplusPModule : public ClangTidyModule {
public:
  void addCheckFactories(ClangTidyCheckFactories &Factories) override {
    Factories.registerCheck<MatcherCheck>("cplusp-matcher");
  }
};

} // namespace

static clang::tidy::ClangTidyModuleRegistry::Add<CplusPModule> X("cplusp-module", "Adds the checks of cplusp.");

// Forces a linker to keep this module when it is linked in. A loaded plugin does not need it.
volatile int CplusPModuleAnchorSource = 0;
