// The clang-tidy plugin of cplusp. See docs/policy.md.
//
// One generic check, driven by the policy file.
// The gate writes each `matcher` entry of a rule as an option of the check, named `{rule_id}/{n}`.
// The check compiles the pattern and reports every match with the rule id as its message.
// The Rust side turns the rule id into the message for the bot.
//
// Seventeen hand-written checks and the translator cplusp-tree. The checks are for the rules that a pattern cannot say. The gate maps a finding to its rule by
// the name of the check, so their messages are short and plain. The sample pair of each rule is the evidence.

#include "CplusPChecks.h"

namespace {

class CplusPModule : public ClangTidyModule {
public:
  void addCheckFactories(ClangTidyCheckFactories &Factories) override {
    cplusp::detail::addSyntaxChecks(Factories);
    cplusp::detail::addRawCopyChecks(Factories);
    cplusp::detail::addStateChecks(Factories);
    cplusp::detail::addTreeCheck(Factories);
  }
};

} // namespace

static clang::tidy::ClangTidyModuleRegistry::Add<CplusPModule> X("cplusp-module", "Adds the checks of cplusp.");

// Forces a linker to keep this module when it is linked in. A loaded plugin does not need it.
volatile int CplusPModuleAnchorSource = 0;
