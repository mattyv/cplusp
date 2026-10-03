//! Verified core of the cplusp gate.
//!
//! Everything in this crate is proved with Verus. The shell (`crates/cplusp`)
//! parses files and runs tools, then hands the data here. The proofs say:
//!
//! - `validate`: no errors if and only if the policy meets every rule in docs/policy.md.
//! - `emit`: the generated config enables every check of every rule that is not
//!   `allow`, and nothing else. Options travel with their check.
//! - `apply_overrides`: a team override changes only the entries it names, and a
//!   loosened entry always carries its reason.
//! - `rule_for_check` and `keep_finding`: a finding maps to the first rule that
//!   enabled its check, and is dropped inside a trusted function only when that
//!   rule is Trusted only.

use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ data model

/// What the policy decided for a construct. Ordered by strictness, see `strictness`.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Decision {
    Allow,
    Restrict,
    TrustedOnly,
    Ban,
}

/// The three kinds of function from docs/plan.md.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Kind {
    Verified,
    Trusted,
    Plain,
}

/// One clang-tidy check option, `key: value`.
#[derive(Debug, PartialEq)]
pub struct CheckOption {
    pub key: String,
    pub value: String,
}

/// One check in a rule's `detect` list.
#[derive(Debug, PartialEq)]
pub struct CheckRef {
    pub name: String,
    pub options: Vec<CheckOption>,
}

/// One entry of `cplusp-policy.yaml`.
#[derive(Debug, PartialEq)]
pub struct Rule {
    pub id: String,
    pub area: String,
    pub decision: Decision,
    pub limit: Option<String>,
    pub why: String,
    pub use_instead: Option<String>,
    pub detect: Vec<CheckRef>,
    /// Set by `apply_overrides` when a team policy loosened this rule.
    pub loosened_because: Option<String>,
    /// True when the gate enforces this row. False for rows the prover or a
    /// trusted contract owns: the gate treats those as `allow`.
    pub gate: bool,
}

#[derive(Debug, PartialEq)]
pub struct Policy {
    pub rules: Vec<Rule>,
}

/// One entry of a team policy that `extends` another.
#[derive(Debug, PartialEq)]
pub struct Override {
    pub id: String,
    pub decision: Decision,
    pub limit: Option<String>,
    pub loosened_because: Option<String>,
}

/// Why the gate refuses to run on a policy. One variant per rule in docs/policy.md.
#[derive(Debug, PartialEq, Eq)]
pub enum PolicyError {
    RestrictWithoutLimit { id: String },
    MissingDetect { id: String },
    MissingUseInstead { id: String },
    DuplicateId { id: String },
    UnknownCheck { id: String, check: String },
    UnknownOverrideId { id: String },
    LoosenedWithoutReason { id: String },
}

/// One `check.key: value` line of the generated clang-tidy config.
#[derive(Debug, PartialEq)]
pub struct ConfigOption {
    pub check: String,
    pub key: String,
    pub value: String,
}

/// The generated clang-tidy config, as data. The shell turns it into YAML text.
#[derive(Debug, PartialEq)]
pub struct Config {
    pub checks: Vec<String>,
    pub options: Vec<ConfigOption>,
}

// ------------------------------------------------------------ spec vocabulary

/// `name` appears in `checks`, compared by content.
pub open spec fn has_name(checks: Seq<String>, name: Seq<char>) -> bool {
    exists|k: int| 0 <= k < checks.len() && #[trigger] checks[k]@ == name
}

/// `name` appears in a rule's `detect` list, compared by content.
pub open spec fn has_check(detect: Seq<CheckRef>, name: Seq<char>) -> bool {
    exists|j: int| 0 <= j < detect.len() && #[trigger] detect[j].name@ == name
}

/// A rule enables its checks when the gate owns it and its decision is anything but `allow`.
pub open spec fn spec_active(r: Rule) -> bool {
    r.gate && r.decision != Decision::Allow
}

/// Strictness order: allow < restrict < trusted_only < ban.
pub open spec fn strictness(d: Decision) -> int {
    match d {
        Decision::Allow => 0,
        Decision::Restrict => 1,
        Decision::TrustedOnly => 2,
        Decision::Ban => 3,
    }
}

/// Content equality for check references. Vectors compare by content, not identity.
pub open spec fn checkref_eq(a: CheckRef, b: CheckRef) -> bool {
    a.name == b.name && a.options@ == b.options@
}

pub open spec fn detect_eq(a: Seq<CheckRef>, b: Seq<CheckRef>) -> bool {
    a.len() == b.len() && forall|j: int| 0 <= j < a.len() ==> checkref_eq(#[trigger] a[j], b[j])
}

/// Content equality for rules.
pub open spec fn rule_eq(a: Rule, b: Rule) -> bool {
    &&& a.id == b.id
    &&& a.area == b.area
    &&& a.decision == b.decision
    &&& a.limit == b.limit
    &&& a.why == b.why
    &&& a.use_instead == b.use_instead
    &&& detect_eq(a.detect@, b.detect@)
    &&& a.loosened_because == b.loosened_because
    &&& a.gate == b.gate
}

pub open spec fn rules_eq(a: Seq<Rule>, b: Seq<Rule>) -> bool {
    a.len() == b.len() && forall|k: int| 0 <= k < a.len() ==> rule_eq(#[trigger] a[k], b[k])
}

/// Everything about a rule that an override may not touch is the same.
pub open spec fn spec_same_identity(a: Rule, b: Rule) -> bool {
    &&& a.id == b.id
    &&& a.area == b.area
    &&& a.why == b.why
    &&& a.use_instead == b.use_instead
    &&& detect_eq(a.detect@, b.detect@)
    &&& a.gate == b.gate
}

/// One rule meets the per-rule requirements of docs/policy.md.
pub open spec fn spec_rule_ok(r: Rule, known: Seq<String>) -> bool {
    &&& (r.decision == Decision::Restrict ==> r.limit is Some)
    &&& (spec_active(r) ==> r.detect.len() > 0)
    &&& (spec_active(r) ==> r.use_instead is Some)
    &&& (forall|j: int| 0 <= j < r.detect.len() ==> has_name(known, #[trigger] r.detect[j].name@))
}

/// No two rules share an id.
pub open spec fn spec_ids_unique(rules: Seq<Rule>) -> bool {
    forall|a: int, b: int| 0 <= a < b < rules.len() ==> #[trigger] rules[a].id@ != #[trigger] rules[b].id@
}

/// The whole policy is acceptable.
pub open spec fn spec_valid(p: Policy, known: Seq<String>) -> bool {
    &&& (forall|i: int| 0 <= i < p.rules.len() ==> spec_rule_ok(#[trigger] p.rules[i], known))
    &&& spec_ids_unique(p.rules@)
}

/// Indices `(i, j)` name a check of an active rule.
pub open spec fn check_at(p: Policy, i: int, j: int) -> bool {
    0 <= i < p.rules.len() && spec_active(p.rules[i]) && 0 <= j < p.rules[i].detect.len()
}

/// The name of the check at `(i, j)`.
pub open spec fn check_name(p: Policy, i: int, j: int) -> Seq<char> {
    p.rules[i].detect[j].name@
}

/// Indices `(i, j, k)` name an option of a check of an active rule.
pub open spec fn option_at(p: Policy, i: int, j: int, k: int) -> bool {
    check_at(p, i, j) && 0 <= k < p.rules[i].detect[j].options.len()
}

pub open spec fn option_key(p: Policy, i: int, j: int, k: int) -> Seq<char> {
    p.rules[i].detect[j].options[k].key@
}

pub open spec fn option_value(p: Policy, i: int, j: int, k: int) -> Seq<char> {
    p.rules[i].detect[j].options[k].value@
}

/// Some rule that is not `allow` names `check`.
pub open spec fn spec_enabled(p: Policy, check: Seq<char>) -> bool {
    exists|i: int, j: int| #[trigger] check_at(p, i, j) && check_name(p, i, j) == check
}

/// A config option line exists for `check.key = value`.
pub open spec fn has_option(opts: Seq<ConfigOption>, check: Seq<char>, key: Seq<char>, value: Seq<char>) -> bool {
    exists|m: int| 0 <= m < opts.len() && #[trigger] opts[m].check@ == check && opts[m].key@ == key && opts[m].value@ == value
}

/// A config option line came from some active rule's check.
pub open spec fn option_from_active(p: Policy, o: ConfigOption) -> bool {
    exists|i: int, j: int, k: int|
        #[trigger] option_at(p, i, j, k)
        && check_name(p, i, j) == o.check@
        && option_key(p, i, j, k) == o.key@
        && option_value(p, i, j, k) == o.value@
}

/// Whether a finding stands, by the kind of function it sits in.
pub open spec fn spec_keep(d: Decision, kind: Kind) -> bool {
    match kind {
        Kind::Verified => true,
        Kind::Trusted => d != Decision::TrustedOnly,
        Kind::Plain => false,
    }
}

/// Some override names this id.
pub open spec fn spec_named(overrides: Seq<Override>, id: Seq<char>) -> bool {
    exists|o: int| 0 <= o < overrides.len() && #[trigger] overrides[o].id@ == id
}

/// The first `upto` overrides each name a rule of `base`.
pub open spec fn spec_overrides_resolve(base: Policy, overrides: Seq<Override>, upto: int) -> bool {
    forall|x: int| 0 <= x < upto
        ==> exists|k: int| 0 <= k < base.rules.len() && #[trigger] base.rules@[k].id@ == #[trigger] overrides[x].id@
}

/// Among the first `upto` overrides, every one that loosens a rule carries a reason.
pub open spec fn spec_loosening_justified(base: Policy, overrides: Seq<Override>, upto: int) -> bool {
    forall|x: int, k: int|
        0 <= x < upto && 0 <= k < base.rules.len()
        && #[trigger] base.rules@[k].id@ == #[trigger] overrides[x].id@
        && strictness(overrides[x].decision) < strictness(base.rules@[k].decision)
        ==> overrides[x].loosened_because is Some
}

// ------------------------------------------------------------------- lemmas

/// Appending to a list keeps every name that was already in it.
proof fn lemma_has_name_extend(before: Seq<String>, after: Seq<String>, name: Seq<char>)
    requires
        has_name(before, name),
        before.len() <= after.len(),
        forall|k: int| 0 <= k < before.len() ==> after[k] == before[k],
    ensures has_name(after, name),
{
    let k = choose|k: int| 0 <= k < before.len() && #[trigger] before[k]@ == name;
    assert(after[k]@ == name);
}

/// Appending to a list keeps every option line that was already in it.
proof fn lemma_has_option_extend(before: Seq<ConfigOption>, after: Seq<ConfigOption>, check: Seq<char>, key: Seq<char>, value: Seq<char>)
    requires
        has_option(before, check, key, value),
        before.len() <= after.len(),
        forall|m: int| 0 <= m < before.len() ==> after[m] == before[m],
    ensures has_option(after, check, key, value),
{
    let m = choose|m: int| 0 <= m < before.len() && #[trigger] before[m].check@ == check && before[m].key@ == key && before[m].value@ == value;
    assert(after[m].check@ == check);
}

/// Growing the processed prefix by one override names exactly one more id.
proof fn lemma_named_step(s: Seq<Override>, o: int, id: Seq<char>)
    requires 0 <= o < s.len(),
    ensures spec_named(s.subrange(0, o + 1), id) == (spec_named(s.subrange(0, o), id) || s[o].id@ == id),
{
    let big = s.subrange(0, o + 1);
    let small = s.subrange(0, o);
    if spec_named(big, id) {
        let x = choose|x: int| 0 <= x < big.len() && #[trigger] big[x].id@ == id;
        if x < o {
            assert(small[x].id@ == id);
        } else {
            assert(big[x] == s[o]);
        }
    }
    if spec_named(small, id) {
        let x = choose|x: int| 0 <= x < small.len() && #[trigger] small[x].id@ == id;
        assert(big[x].id@ == id);
    }
    if s[o].id@ == id {
        assert(big[o].id@ == id);
    }
}

// ------------------------------------------------------------- small helpers

/// Exec twin of `strictness`.
pub fn strictness_level(d: Decision) -> (n: u8)
    ensures n as int == strictness(d),
{
    match d {
        Decision::Allow => 0,
        Decision::Restrict => 1,
        Decision::TrustedOnly => 2,
        Decision::Ban => 3,
    }
}

/// `new` is looser than `old` when it is lower in the strictness order.
pub fn is_looser(new: Decision, old: Decision) -> (res: bool)
    ensures res == (strictness(new) < strictness(old)),
{
    strictness_level(new) < strictness_level(old)
}

/// Exec twin of `has_name`.
pub fn contains_name(checks: &Vec<String>, name: &String) -> (res: bool)
    ensures res == has_name(checks@, name@),
{
    let mut i: usize = 0;
    while i < checks.len()
        invariant
            0 <= i <= checks.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] checks@[k]@ != name@,
        decreases checks.len() - i,
    {
        if checks[i] == *name {
            return true;
        }
        i += 1;
    }
    false
}

/// Exec twin of `has_check`.
pub fn detect_contains(detect: &Vec<CheckRef>, name: &String) -> (res: bool)
    ensures res == has_check(detect@, name@),
{
    let mut j: usize = 0;
    while j < detect.len()
        invariant
            0 <= j <= detect.len(),
            forall|k: int| 0 <= k < j ==> #[trigger] detect@[k].name@ != name@,
        decreases detect.len() - j,
    {
        if detect[j].name == *name {
            return true;
        }
        j += 1;
    }
    false
}

/// Exec twin of `spec_active`.
pub fn is_active(r: &Rule) -> (res: bool)
    ensures res == spec_active(*r),
{
    r.gate && r.decision != Decision::Allow
}

fn clone_opt_string(s: &Option<String>) -> (res: Option<String>)
    ensures res == *s,
{
    match s {
        Some(x) => Some(x.clone()),
        None => None,
    }
}

fn clone_options(v: &Vec<CheckOption>) -> (res: Vec<CheckOption>)
    ensures res@ == v@,
{
    let mut out: Vec<CheckOption> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant 0 <= i <= v.len(), out@ == v@.subrange(0, i as int),
        decreases v.len() - i,
    {
        out.push(CheckOption { key: v[i].key.clone(), value: v[i].value.clone() });
        i += 1;
    }
    assert(out@ =~= v@);
    out
}

fn clone_detect(v: &Vec<CheckRef>) -> (res: Vec<CheckRef>)
    ensures detect_eq(res@, v@),
{
    let mut out: Vec<CheckRef> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            out.len() == i,
            forall|j: int| 0 <= j < i ==> checkref_eq(#[trigger] out@[j], v@[j]),
        decreases v.len() - i,
    {
        out.push(CheckRef { name: v[i].name.clone(), options: clone_options(&v[i].options) });
        i += 1;
    }
    out
}

/// A copy of `r` with the fields an override may change replaced.
fn rule_with(r: &Rule, decision: Decision, limit: Option<String>, loosened_because: Option<String>) -> (res: Rule)
    ensures
        spec_same_identity(res, *r),
        res.decision == decision,
        res.limit == limit,
        res.loosened_because == loosened_because,
{
    Rule {
        id: r.id.clone(),
        area: r.area.clone(),
        decision,
        limit,
        why: r.why.clone(),
        use_instead: clone_opt_string(&r.use_instead),
        detect: clone_detect(&r.detect),
        loosened_because,
        gate: r.gate,
    }
}

/// A copy of a rule, equal in content.
pub fn clone_rule(r: &Rule) -> (res: Rule)
    ensures rule_eq(res, *r),
{
    rule_with(r, r.decision, clone_opt_string(&r.limit), clone_opt_string(&r.loosened_because))
}

/// A copy of a policy, equal in content.
pub fn clone_policy(p: &Policy) -> (res: Policy)
    ensures rules_eq(res.rules@, p.rules@),
{
    let mut out: Vec<Rule> = Vec::new();
    let mut i: usize = 0;
    while i < p.rules.len()
        invariant
            0 <= i <= p.rules.len(),
            out.len() == i,
            forall|k: int| 0 <= k < i ==> rule_eq(#[trigger] out@[k], p.rules@[k]),
        decreases p.rules.len() - i,
    {
        out.push(clone_rule(&p.rules[i]));
        i += 1;
    }
    Policy { rules: out }
}

// --------------------------------------------------------------- validation

/// Every check in `detect` is one the toolchain knows.
fn all_known(detect: &Vec<CheckRef>, known: &Vec<String>) -> (res: Option<usize>)
    ensures
        match res {
            None => forall|j: int| 0 <= j < detect.len() ==> has_name(known@, #[trigger] detect@[j].name@),
            Some(j) => j < detect.len() && !has_name(known@, detect@[j as int].name@),
        },
{
    let mut j: usize = 0;
    while j < detect.len()
        invariant
            0 <= j <= detect.len(),
            forall|k: int| 0 <= k < j ==> has_name(known@, #[trigger] detect@[k].name@),
        decreases detect.len() - j,
    {
        if !contains_name(known, &detect[j].name) {
            return Some(j);
        }
        j += 1;
    }
    None
}

/// Appends the errors of one rule. No new error if and only if the rule is ok.
fn rule_errors(r: &Rule, known: &Vec<String>, errors: &mut Vec<PolicyError>)
    ensures
        final(errors).len() >= old(errors).len(),
        (final(errors).len() == old(errors).len()) <==> spec_rule_ok(*r, known@),
{
    let active = is_active(r);
    if r.decision == Decision::Restrict && r.limit.is_none() {
        errors.push(PolicyError::RestrictWithoutLimit { id: r.id.clone() });
    }
    if active && r.detect.len() == 0 {
        errors.push(PolicyError::MissingDetect { id: r.id.clone() });
    }
    if active && r.use_instead.is_none() {
        errors.push(PolicyError::MissingUseInstead { id: r.id.clone() });
    }
    match all_known(&r.detect, known) {
        Some(j) => {
            errors.push(PolicyError::UnknownCheck { id: r.id.clone(), check: r.detect[j].name.clone() });
        }
        None => {}
    }
}

/// Some earlier rule has the same id as rule `i`.
fn duplicate_before(rules: &Vec<Rule>, i: usize) -> (res: bool)
    requires i < rules.len(),
    ensures res == exists|a: int| 0 <= a < i && #[trigger] rules@[a].id@ == rules@[i as int].id@,
{
    let mut a: usize = 0;
    while a < i
        invariant
            0 <= a <= i < rules.len(),
            forall|k: int| 0 <= k < a ==> #[trigger] rules@[k].id@ != rules@[i as int].id@,
        decreases i - a,
    {
        if rules[a].id == rules[i].id {
            return true;
        }
        a += 1;
    }
    false
}

/// Every reason the gate would refuse this policy. Empty if and only if the policy is valid.
pub fn validate(p: &Policy, known: &Vec<String>) -> (errors: Vec<PolicyError>)
    ensures (errors.len() == 0) <==> spec_valid(*p, known@),
{
    let mut errors: Vec<PolicyError> = Vec::new();
    let mut i: usize = 0;
    while i < p.rules.len()
        invariant
            0 <= i <= p.rules.len(),
            (errors.len() == 0) <==> (
                (forall|k: int| 0 <= k < i ==> spec_rule_ok(#[trigger] p.rules@[k], known@))
                && (forall|a: int, b: int| 0 <= a < b < i ==> #[trigger] p.rules@[a].id@ != #[trigger] p.rules@[b].id@)
            ),
        decreases p.rules.len() - i,
    {
        rule_errors(&p.rules[i], known, &mut errors);
        if duplicate_before(&p.rules, i) {
            errors.push(PolicyError::DuplicateId { id: p.rules[i].id.clone() });
        }
        i += 1;
    }
    errors
}

// ----------------------------------------------------------------- emission

/// The checks to enable: every check of every active rule, each once, in order of first appearance.
fn collect_checks(p: &Policy) -> (checks: Vec<String>)
    ensures
        forall|i: int, j: int| #[trigger] check_at(*p, i, j) ==> has_name(checks@, check_name(*p, i, j)),
        forall|k: int| 0 <= k < checks.len() ==> spec_enabled(*p, #[trigger] checks@[k]@),
        forall|a: int, b: int| 0 <= a < b < checks.len() ==> #[trigger] checks@[a]@ != #[trigger] checks@[b]@,
{
    let mut checks: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < p.rules.len()
        invariant
            0 <= i <= p.rules.len(),
            forall|x: int, y: int| x < i && #[trigger] check_at(*p, x, y) ==> has_name(checks@, check_name(*p, x, y)),
            forall|k: int| 0 <= k < checks.len() ==> spec_enabled(*p, #[trigger] checks@[k]@),
            forall|a: int, b: int| 0 <= a < b < checks.len() ==> #[trigger] checks@[a]@ != #[trigger] checks@[b]@,
        decreases p.rules.len() - i,
    {
        if is_active(&p.rules[i]) {
            let detect = &p.rules[i].detect;
            let mut j: usize = 0;
            while j < detect.len()
                invariant
                    0 <= j <= detect.len(),
                    i < p.rules.len(),
                    spec_active(p.rules@[i as int]),
                    detect@ == p.rules@[i as int].detect@,
                    forall|x: int, y: int| x < i && #[trigger] check_at(*p, x, y) ==> has_name(checks@, check_name(*p, x, y)),
                    forall|y: int| 0 <= y < j ==> has_name(checks@, #[trigger] detect@[y].name@),
                    forall|k: int| 0 <= k < checks.len() ==> spec_enabled(*p, #[trigger] checks@[k]@),
                    forall|a: int, b: int| 0 <= a < b < checks.len() ==> #[trigger] checks@[a]@ != #[trigger] checks@[b]@,
                decreases detect.len() - j,
            {
                let name = detect[j].name.clone();
                if !contains_name(&checks, &name) {
                    let ghost before = checks@;
                    checks.push(name);
                    proof {
                        let n = before.len() as int;
                        assert(checks@[n]@ == detect@[j as int].name@);
                        assert(check_at(*p, i as int, j as int));
                        assert(spec_enabled(*p, detect@[j as int].name@));
                        assert forall|x: int, y: int| x < i && #[trigger] check_at(*p, x, y)
                            implies has_name(checks@, check_name(*p, x, y)) by {
                            lemma_has_name_extend(before, checks@, check_name(*p, x, y));
                        }
                        assert forall|y: int| 0 <= y <= j implies has_name(checks@, #[trigger] detect@[y].name@) by {
                            if y < j {
                                lemma_has_name_extend(before, checks@, detect@[y].name@);
                            }
                        }
                        assert forall|k: int| 0 <= k < checks.len() implies spec_enabled(*p, #[trigger] checks@[k]@) by {
                            if k < n {
                                assert(checks@[k] == before[k]);
                            }
                        }
                        assert forall|a: int, b: int| 0 <= a < b < checks.len()
                            implies #[trigger] checks@[a]@ != #[trigger] checks@[b]@ by {
                            if b == n {
                                assert(!has_name(before, detect@[j as int].name@));
                                assert(before[a]@ != detect@[j as int].name@);
                            }
                        }
                    }
                }
                j += 1;
            }
            proof {
                assert forall|y: int| #[trigger] check_at(*p, i as int, y)
                    implies has_name(checks@, check_name(*p, i as int, y)) by {
                    assert(has_name(checks@, detect@[y].name@));
                }
            }
        } else {
            proof {
                assert forall|y: int| #[trigger] check_at(*p, i as int, y)
                    implies has_name(checks@, check_name(*p, i as int, y)) by {
                    assert(!spec_active(p.rules@[i as int]));
                }
            }
        }
        i += 1;
    }
    checks
}

/// The option lines to emit: every option of every check of every active rule.
fn collect_options(p: &Policy) -> (opts: Vec<ConfigOption>)
    ensures
        forall|i: int, j: int, k: int| #[trigger] option_at(*p, i, j, k)
            ==> has_option(opts@, check_name(*p, i, j), option_key(*p, i, j, k), option_value(*p, i, j, k)),
        forall|m: int| 0 <= m < opts.len() ==> option_from_active(*p, #[trigger] opts@[m]),
{
    let mut opts: Vec<ConfigOption> = Vec::new();
    let mut i: usize = 0;
    while i < p.rules.len()
        invariant
            0 <= i <= p.rules.len(),
            forall|x: int, y: int, z: int| x < i && #[trigger] option_at(*p, x, y, z)
                ==> has_option(opts@, check_name(*p, x, y), option_key(*p, x, y, z), option_value(*p, x, y, z)),
            forall|m: int| 0 <= m < opts.len() ==> option_from_active(*p, #[trigger] opts@[m]),
        decreases p.rules.len() - i,
    {
        if is_active(&p.rules[i]) {
            let detect = &p.rules[i].detect;
            let mut j: usize = 0;
            while j < detect.len()
                invariant
                    0 <= j <= detect.len(),
                    i < p.rules.len(),
                    spec_active(p.rules@[i as int]),
                    detect@ == p.rules@[i as int].detect@,
                    forall|x: int, y: int, z: int| x < i && #[trigger] option_at(*p, x, y, z)
                        ==> has_option(opts@, check_name(*p, x, y), option_key(*p, x, y, z), option_value(*p, x, y, z)),
                    forall|y: int, z: int| y < j && #[trigger] option_at(*p, i as int, y, z)
                        ==> has_option(opts@, check_name(*p, i as int, y), option_key(*p, i as int, y, z), option_value(*p, i as int, y, z)),
                    forall|m: int| 0 <= m < opts.len() ==> option_from_active(*p, #[trigger] opts@[m]),
                decreases detect.len() - j,
            {
                let options = &detect[j].options;
                let mut k: usize = 0;
                while k < options.len()
                    invariant
                        0 <= k <= options.len(),
                        0 <= j < detect.len(),
                        i < p.rules.len(),
                        spec_active(p.rules@[i as int]),
                        detect@ == p.rules@[i as int].detect@,
                        options@ == detect@[j as int].options@,
                        forall|x: int, y: int, z: int| x < i && #[trigger] option_at(*p, x, y, z)
                            ==> has_option(opts@, check_name(*p, x, y), option_key(*p, x, y, z), option_value(*p, x, y, z)),
                        forall|y: int, z: int| y < j && #[trigger] option_at(*p, i as int, y, z)
                            ==> has_option(opts@, check_name(*p, i as int, y), option_key(*p, i as int, y, z), option_value(*p, i as int, y, z)),
                        forall|z: int| z < k && #[trigger] option_at(*p, i as int, j as int, z)
                            ==> has_option(opts@, check_name(*p, i as int, j as int), option_key(*p, i as int, j as int, z), option_value(*p, i as int, j as int, z)),
                        forall|m: int| 0 <= m < opts.len() ==> option_from_active(*p, #[trigger] opts@[m]),
                    decreases options.len() - k,
                {
                    let line = ConfigOption {
                        check: detect[j].name.clone(),
                        key: options[k].key.clone(),
                        value: options[k].value.clone(),
                    };
                    let ghost before = opts@;
                    let ghost pushed = line;
                    opts.push(line);
                    proof {
                        let n = before.len() as int;
                        assert(opts@[n] == pushed);
                        assert(option_at(*p, i as int, j as int, k as int));
                        assert(pushed.check@ == check_name(*p, i as int, j as int));
                        assert(pushed.key@ == option_key(*p, i as int, j as int, k as int));
                        assert(pushed.value@ == option_value(*p, i as int, j as int, k as int));
                        assert(option_from_active(*p, pushed));
                        assert(has_option(opts@, check_name(*p, i as int, j as int), option_key(*p, i as int, j as int, k as int), option_value(*p, i as int, j as int, k as int)));
                        assert forall|x: int, y: int, z: int| x < i && #[trigger] option_at(*p, x, y, z)
                            implies has_option(opts@, check_name(*p, x, y), option_key(*p, x, y, z), option_value(*p, x, y, z)) by {
                            lemma_has_option_extend(before, opts@, check_name(*p, x, y), option_key(*p, x, y, z), option_value(*p, x, y, z));
                        }
                        assert forall|y: int, z: int| y < j && #[trigger] option_at(*p, i as int, y, z)
                            implies has_option(opts@, check_name(*p, i as int, y), option_key(*p, i as int, y, z), option_value(*p, i as int, y, z)) by {
                            lemma_has_option_extend(before, opts@, check_name(*p, i as int, y), option_key(*p, i as int, y, z), option_value(*p, i as int, y, z));
                        }
                        assert forall|z: int| z <= k && #[trigger] option_at(*p, i as int, j as int, z)
                            implies has_option(opts@, check_name(*p, i as int, j as int), option_key(*p, i as int, j as int, z), option_value(*p, i as int, j as int, z)) by {
                            if z < k {
                                lemma_has_option_extend(before, opts@, check_name(*p, i as int, j as int), option_key(*p, i as int, j as int, z), option_value(*p, i as int, j as int, z));
                            }
                        }
                        assert forall|m: int| 0 <= m < opts.len() implies option_from_active(*p, #[trigger] opts@[m]) by {
                            if m < n {
                                assert(opts@[m] == before[m]);
                            }
                        }
                    }
                    k += 1;
                }
                proof {
                    assert forall|z: int| #[trigger] option_at(*p, i as int, j as int, z)
                        implies has_option(opts@, check_name(*p, i as int, j as int), option_key(*p, i as int, j as int, z), option_value(*p, i as int, j as int, z)) by {
                        assert(z < options.len());
                    }
                }
                j += 1;
            }
            proof {
                assert forall|y: int, z: int| #[trigger] option_at(*p, i as int, y, z)
                    implies has_option(opts@, check_name(*p, i as int, y), option_key(*p, i as int, y, z), option_value(*p, i as int, y, z)) by {
                    assert(y < detect.len());
                }
            }
        } else {
            proof {
                assert forall|y: int, z: int| #[trigger] option_at(*p, i as int, y, z)
                    implies has_option(opts@, check_name(*p, i as int, y), option_key(*p, i as int, y, z), option_value(*p, i as int, y, z)) by {
                    assert(!spec_active(p.rules@[i as int]));
                }
            }
        }
        i += 1;
    }
    opts
}

/// The clang-tidy config for a policy. See the ensures of `collect_checks` and `collect_options`.
pub fn emit(p: &Policy) -> (c: Config)
    ensures
        forall|i: int, j: int| #[trigger] check_at(*p, i, j) ==> has_name(c.checks@, check_name(*p, i, j)),
        forall|k: int| 0 <= k < c.checks.len() ==> spec_enabled(*p, #[trigger] c.checks@[k]@),
        forall|a: int, b: int| 0 <= a < b < c.checks.len() ==> #[trigger] c.checks@[a]@ != #[trigger] c.checks@[b]@,
        forall|i: int, j: int, k: int| #[trigger] option_at(*p, i, j, k)
            ==> has_option(c.options@, check_name(*p, i, j), option_key(*p, i, j, k), option_value(*p, i, j, k)),
        forall|m: int| 0 <= m < c.options.len() ==> option_from_active(*p, #[trigger] c.options@[m]),
{
    Config { checks: collect_checks(p), options: collect_options(p) }
}

// ---------------------------------------------------------------- overrides

/// Index of the rule with this id, if any.
fn find_rule(rules: &Vec<Rule>, id: &String) -> (res: Option<usize>)
    ensures
        match res {
            Some(i) => i < rules.len() && rules@[i as int].id@ == id@,
            None => forall|k: int| 0 <= k < rules.len() ==> #[trigger] rules@[k].id@ != id@,
        },
{
    let mut i: usize = 0;
    while i < rules.len()
        invariant
            0 <= i <= rules.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] rules@[k].id@ != id@,
        decreases rules.len() - i,
    {
        if rules[i].id == *id {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// A team policy applied to a base policy whose ids are unique.
///
/// On success: the same rules in the same order, every rule an override does not
/// name is unchanged in content, a named rule keeps its identity (id, area, why,
/// use_instead, detect), every override names a real rule, and every loosening
/// override carries a reason. On failure, the errors say which override was wrong.
pub fn apply_overrides(base: &Policy, overrides: &Vec<Override>) -> (res: Result<Policy, Vec<PolicyError>>)
    requires spec_ids_unique(base.rules@),
    ensures
        res matches Err(errors) ==> errors.len() > 0,
        res matches Ok(p) ==> p.rules.len() == base.rules.len(),
        res matches Ok(p) ==> forall|k: int| 0 <= k < p.rules.len() && !spec_named(overrides@, base.rules@[k].id@)
            ==> rule_eq(#[trigger] p.rules@[k], base.rules@[k]),
        res matches Ok(p) ==> forall|k: int| 0 <= k < p.rules.len() ==> spec_same_identity(#[trigger] p.rules@[k], base.rules@[k]),
        res matches Ok(p) ==> spec_overrides_resolve(*base, overrides@, overrides.len() as int),
        res matches Ok(p) ==> spec_loosening_justified(*base, overrides@, overrides.len() as int),
{
    let mut out = clone_policy(base);
    let mut errors: Vec<PolicyError> = Vec::new();
    let mut o: usize = 0;
    while o < overrides.len()
        invariant
            0 <= o <= overrides.len(),
            spec_ids_unique(base.rules@),
            out.rules.len() == base.rules.len(),
            forall|k: int| 0 <= k < out.rules.len() && !spec_named(overrides@.subrange(0, o as int), base.rules@[k].id@)
                ==> rule_eq(#[trigger] out.rules@[k], base.rules@[k]),
            forall|k: int| 0 <= k < out.rules.len() ==> spec_same_identity(#[trigger] out.rules@[k], base.rules@[k]),
            errors.len() == 0 ==> spec_overrides_resolve(*base, overrides@, o as int),
            errors.len() == 0 ==> spec_loosening_justified(*base, overrides@, o as int),
        decreases overrides.len() - o,
    {
        let ov = &overrides[o];
        let ghost before = out.rules@;
        let ghost had_errors = errors.len() > 0;
        match find_rule(&base.rules, &ov.id) {
            None => {
                errors.push(PolicyError::UnknownOverrideId { id: ov.id.clone() });
            }
            Some(k) => {
                let current = &base.rules[k];
                let looser = is_looser(ov.decision, current.decision);
                if looser && ov.loosened_because.is_none() {
                    errors.push(PolicyError::LoosenedWithoutReason { id: ov.id.clone() });
                } else {
                    let limit = match &ov.limit {
                        Some(l) => Some(l.clone()),
                        None => clone_opt_string(&current.limit),
                    };
                    let reason = if looser { clone_opt_string(&ov.loosened_because) } else { None };
                    let replaced = rule_with(current, ov.decision, limit, reason);
                    out.rules.set(k, replaced);
                    proof {
                        // With unique ids, `k` is the only rule this override names.
                        assert forall|kp: int| 0 <= kp < base.rules.len() && #[trigger] base.rules@[kp].id@ == ov.id@
                            implies kp == k by {
                            if kp < k {
                                assert(base.rules@[kp].id@ != base.rules@[k as int].id@);
                            } else if kp > k {
                                assert(base.rules@[k as int].id@ != base.rules@[kp].id@);
                            }
                        }
                        assert forall|kk: int| 0 <= kk < out.rules.len()
                            implies spec_same_identity(#[trigger] out.rules@[kk], base.rules@[kk]) by {
                            if kk != k {
                                assert(out.rules@[kk] == before[kk]);
                            }
                        }
                        // The two facts the postcondition needs about this override.
                        assert(base.rules@[k as int].id@ == overrides@[o as int].id@);
                        if errors@.len() == 0 {
                            assert forall|x: int| 0 <= x < o as int + 1
                                implies exists|kk: int| 0 <= kk < base.rules.len()
                                    && #[trigger] base.rules@[kk].id@ == #[trigger] overrides@[x].id@ by {
                                if x < o as int {
                                    assert(spec_overrides_resolve(*base, overrides@, o as int));
                                } else {
                                    assert(base.rules@[k as int].id@ == overrides@[x].id@);
                                }
                            }
                            assert(spec_overrides_resolve(*base, overrides@, o as int + 1));
                            assert forall|x: int, kp: int|
                                0 <= x < o as int + 1 && 0 <= kp < base.rules.len()
                                && #[trigger] base.rules@[kp].id@ == #[trigger] overrides@[x].id@
                                && strictness(overrides@[x].decision) < strictness(base.rules@[kp].decision)
                                implies overrides@[x].loosened_because is Some by {
                                if x < o as int {
                                    assert(spec_loosening_justified(*base, overrides@, o as int));
                                } else {
                                    assert(kp == k);
                                    assert(looser);
                                }
                            }
                            assert(spec_loosening_justified(*base, overrides@, o as int + 1));
                        }
                    }
                }
            }
        }
        proof {
            assert(overrides@.subrange(0, o as int + 1) =~= overrides@.subrange(0, o as int).push(overrides@[o as int]));
            assert forall|k: int| 0 <= k < out.rules.len() && !spec_named(overrides@.subrange(0, o as int + 1), base.rules@[k].id@)
                implies rule_eq(#[trigger] out.rules@[k], base.rules@[k]) by {
                lemma_named_step(overrides@, o as int, base.rules@[k].id@);
                assert(!spec_named(overrides@.subrange(0, o as int), base.rules@[k].id@));
                assert(base.rules@[k].id@ != ov.id@);
                assert(out.rules@[k] == before[k]);
            }
        }
        o += 1;
    }
    proof {
        assert(overrides@.subrange(0, o as int) =~= overrides@);
    }
    if errors.len() == 0 {
        Ok(out)
    } else {
        Err(errors)
    }
}

// ----------------------------------------------------------------- findings

/// The first rule that is not `allow` and names this check.
pub fn rule_for_check(p: &Policy, check: &String) -> (res: Option<usize>)
    ensures
        match res {
            Some(i) => {
                &&& i < p.rules.len()
                &&& spec_active(p.rules@[i as int])
                &&& has_check(p.rules@[i as int].detect@, check@)
                &&& forall|k: int| 0 <= k < i ==> !(spec_active(#[trigger] p.rules@[k]) && has_check(p.rules@[k].detect@, check@))
            },
            None => !spec_enabled(*p, check@),
        },
{
    let mut i: usize = 0;
    while i < p.rules.len()
        invariant
            0 <= i <= p.rules.len(),
            forall|k: int| 0 <= k < i ==> !(spec_active(#[trigger] p.rules@[k]) && has_check(p.rules@[k].detect@, check@)),
        decreases p.rules.len() - i,
    {
        if is_active(&p.rules[i]) && detect_contains(&p.rules[i].detect, check) {
            return Some(i);
        }
        i += 1;
    }
    proof {
        // Nothing enabled this check: any witness (x, y) would be an active rule with the name.
        assert forall|x: int, y: int| #[trigger] check_at(*p, x, y) implies check_name(*p, x, y) != check@ by {
            if check_name(*p, x, y) == check@ {
                assert(has_check(p.rules@[x].detect@, check@));
            }
        }
    }
    None
}

/// Whether a finding of a rule with decision `d` stands in a function of kind `kind`.
pub fn keep_finding(d: Decision, kind: Kind) -> (res: bool)
    ensures res == spec_keep(d, kind),
{
    match kind {
        Kind::Verified => true,
        Kind::Trusted => d != Decision::TrustedOnly,
        Kind::Plain => false,
    }
}

} // verus!
