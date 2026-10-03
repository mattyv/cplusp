//! Behaviour of the verified core, as the docs describe it.
//! docs/policy.md is the reference for every expectation here.

use cplusp_core::*;

fn rule(id: &str, decision: Decision, checks: &[&str]) -> Rule {
    Rule {
        id: id.to_string(),
        area: "control".to_string(),
        decision,
        limit: if decision == Decision::Restrict { Some("the limit".to_string()) } else { None },
        why: "because".to_string(),
        use_instead: if decision == Decision::Allow { None } else { Some("something else".to_string()) },
        detect: checks.iter().map(|c| CheckRef { name: c.to_string(), options: vec![] }).collect(),
        loosened_because: None,
        gate: true,
    }
}

/// A row the prover or a trusted contract owns. The gate has nothing to detect.
fn prover_rule(id: &str, decision: Decision) -> Rule {
    let mut r = rule(id, decision, &[]);
    r.gate = false;
    r.use_instead = None;
    r
}

fn policy(rules: Vec<Rule>) -> Policy {
    Policy { rules }
}

fn names(v: &[&str]) -> Vec<String> {
    v.iter().map(|s| s.to_string()).collect()
}

const KNOWN: &[&str] = &[
    "cppcoreguidelines-avoid-goto",
    "google-readability-casting",
    "cppcoreguidelines-pro-type-union-access",
    "cplusp-union-decl",
    "cplusp-iterator-arithmetic",
    "cppcoreguidelines-pro-bounds-constant-array-index",
];

// ---------------------------------------------------------------- validation

#[test]
fn a_valid_policy_has_no_errors() {
    let p = policy(vec![
        rule("goto", Decision::Ban, &["cppcoreguidelines-avoid-goto"]),
        rule("iterators", Decision::Restrict, &["cplusp-iterator-arithmetic"]),
        rule("variable_index", Decision::Allow, &["cppcoreguidelines-pro-bounds-constant-array-index"]),
    ]);
    assert_eq!(validate(&p, &names(KNOWN)), vec![]);
}

#[test]
fn a_restrict_rule_without_a_limit_is_rejected() {
    let mut r = rule("iterators", Decision::Restrict, &["cplusp-iterator-arithmetic"]);
    r.limit = None;
    let errors = validate(&policy(vec![r]), &names(KNOWN));
    assert_eq!(errors, vec![PolicyError::RestrictWithoutLimit { id: "iterators".to_string() }]);
}

#[test]
fn a_ban_without_detect_is_rejected() {
    let errors = validate(&policy(vec![rule("goto", Decision::Ban, &[])]), &names(KNOWN));
    assert_eq!(errors, vec![PolicyError::MissingDetect { id: "goto".to_string() }]);
}

#[test]
fn a_trusted_only_rule_without_use_instead_is_rejected() {
    let mut r = rule("unions", Decision::TrustedOnly, &["cplusp-union-decl"]);
    r.use_instead = None;
    let errors = validate(&policy(vec![r]), &names(KNOWN));
    assert_eq!(errors, vec![PolicyError::MissingUseInstead { id: "unions".to_string() }]);
}

#[test]
fn an_allow_rule_needs_neither_detect_nor_use_instead() {
    let errors = validate(&policy(vec![rule("constexpr", Decision::Allow, &[])]), &names(KNOWN));
    assert_eq!(errors, vec![]);
}

#[test]
fn a_prover_stage_restrict_rule_needs_a_limit_but_no_detect() {
    let ok = prover_rule("floating_point", Decision::Restrict);
    assert_eq!(validate(&policy(vec![ok]), &names(KNOWN)), vec![]);
    let mut bad = prover_rule("floating_point", Decision::Restrict);
    bad.limit = None;
    assert_eq!(
        validate(&policy(vec![bad]), &names(KNOWN)),
        vec![PolicyError::RestrictWithoutLimit { id: "floating_point".to_string() }]
    );
}

#[test]
fn emit_enables_nothing_for_a_prover_stage_rule() {
    let mut r = prover_rule("floating_point", Decision::Restrict);
    r.detect.push(CheckRef { name: "google-readability-casting".to_string(), options: vec![] });
    assert_eq!(emit(&policy(vec![r])).checks, Vec::<String>::new());
}

#[test]
fn a_finding_from_a_prover_stage_rule_check_maps_to_nothing() {
    let mut r = prover_rule("floating_point", Decision::Restrict);
    r.detect.push(CheckRef { name: "google-readability-casting".to_string(), options: vec![] });
    assert_eq!(rule_for_check(&policy(vec![r]), &"google-readability-casting".to_string()), None);
}

#[test]
fn duplicate_ids_are_rejected() {
    let p = policy(vec![
        rule("goto", Decision::Ban, &["cppcoreguidelines-avoid-goto"]),
        rule("goto", Decision::Ban, &["cppcoreguidelines-avoid-goto"]),
    ]);
    assert_eq!(validate(&p, &names(KNOWN)), vec![PolicyError::DuplicateId { id: "goto".to_string() }]);
}

#[test]
fn a_check_the_toolchain_does_not_know_is_rejected() {
    let p = policy(vec![rule("goto", Decision::Ban, &["misspelt-check"])]);
    assert_eq!(
        validate(&p, &names(KNOWN)),
        vec![PolicyError::UnknownCheck { id: "goto".to_string(), check: "misspelt-check".to_string() }]
    );
}

#[test]
fn every_error_is_reported_not_only_the_first() {
    let mut r1 = rule("iterators", Decision::Restrict, &["cplusp-iterator-arithmetic"]);
    r1.limit = None;
    let r2 = rule("goto", Decision::Ban, &[]);
    let errors = validate(&policy(vec![r1, r2]), &names(KNOWN));
    assert_eq!(errors.len(), 2);
    assert!(errors.contains(&PolicyError::RestrictWithoutLimit { id: "iterators".to_string() }));
    assert!(errors.contains(&PolicyError::MissingDetect { id: "goto".to_string() }));
}

// ------------------------------------------------------------------- emission

#[test]
fn emit_enables_every_check_of_every_rule_that_is_not_allow() {
    let p = policy(vec![
        rule("goto", Decision::Ban, &["cppcoreguidelines-avoid-goto"]),
        rule("unions", Decision::Ban, &["cppcoreguidelines-pro-type-union-access", "cplusp-union-decl"]),
        rule("iterators", Decision::Restrict, &["cplusp-iterator-arithmetic"]),
    ]);
    let config = emit(&p);
    assert_eq!(
        config.checks,
        names(&[
            "cppcoreguidelines-avoid-goto",
            "cppcoreguidelines-pro-type-union-access",
            "cplusp-union-decl",
            "cplusp-iterator-arithmetic",
        ])
    );
}

#[test]
fn emit_enables_nothing_for_an_allow_rule_even_if_it_names_a_check() {
    let p = policy(vec![rule("variable_index", Decision::Allow, &["cppcoreguidelines-pro-bounds-constant-array-index"])]);
    assert_eq!(emit(&p).checks, Vec::<String>::new());
}

#[test]
fn emit_lists_a_check_once_when_two_rules_share_it() {
    let p = policy(vec![
        rule("a", Decision::Ban, &["google-readability-casting"]),
        rule("b", Decision::TrustedOnly, &["google-readability-casting"]),
    ]);
    assert_eq!(emit(&p).checks, names(&["google-readability-casting"]));
}

#[test]
fn emit_carries_the_options_of_every_enabled_check() {
    let mut r = rule("multiple_inheritance", Decision::Restrict, &["cplusp-multiple-inheritance"]);
    r.detect[0].options.push(CheckOption { key: "AllowPureInterfaces".to_string(), value: "true".to_string() });
    let config = emit(&policy(vec![r]));
    assert_eq!(
        config.options,
        vec![ConfigOption {
            check: "cplusp-multiple-inheritance".to_string(),
            key: "AllowPureInterfaces".to_string(),
            value: "true".to_string(),
        }]
    );
}

#[test]
fn emit_drops_the_options_of_a_dormant_check() {
    let mut r = rule("variable_index", Decision::Allow, &["cppcoreguidelines-pro-bounds-constant-array-index"]);
    r.detect[0].options.push(CheckOption { key: "GslHeader".to_string(), value: "gsl.h".to_string() });
    assert_eq!(emit(&policy(vec![r])).options, vec![]);
}

// ------------------------------------------------------------------ overrides

fn base() -> Policy {
    policy(vec![
        rule("goto", Decision::Ban, &["cppcoreguidelines-avoid-goto"]),
        rule("iterators", Decision::Restrict, &["cplusp-iterator-arithmetic"]),
        rule("variable_index", Decision::Allow, &["cppcoreguidelines-pro-bounds-constant-array-index"]),
    ])
}

fn over(id: &str, decision: Decision, reason: Option<&str>) -> Override {
    Override { id: id.to_string(), decision, limit: None, loosened_because: reason.map(|s| s.to_string()) }
}

#[test]
fn an_override_changes_only_the_rule_it_names() {
    let result = apply_overrides(&base(), &vec![over("iterators", Decision::Ban, None)]).unwrap();
    assert_eq!(result.rules[1].decision, Decision::Ban);
    assert_eq!(result.rules[0], base().rules[0]);
    assert_eq!(result.rules[2], base().rules[2]);
    assert_eq!(result.rules.len(), 3);
}

#[test]
fn tightening_needs_no_reason() {
    let result = apply_overrides(&base(), &vec![over("variable_index", Decision::Ban, None)]);
    assert!(result.is_ok());
}

#[test]
fn loosening_without_a_reason_is_rejected() {
    let errors = apply_overrides(&base(), &vec![over("goto", Decision::Allow, None)]).unwrap_err();
    assert_eq!(errors, vec![PolicyError::LoosenedWithoutReason { id: "goto".to_string() }]);
}

#[test]
fn loosening_with_a_reason_is_applied_and_the_reason_kept() {
    let result = apply_overrides(&base(), &vec![over("goto", Decision::Allow, Some("legacy tests use it"))]).unwrap();
    assert_eq!(result.rules[0].decision, Decision::Allow);
    assert_eq!(result.rules[0].loosened_because, Some("legacy tests use it".to_string()));
}

#[test]
fn an_override_of_an_unknown_id_is_rejected() {
    let errors = apply_overrides(&base(), &vec![over("gotos", Decision::Ban, None)]).unwrap_err();
    assert_eq!(errors, vec![PolicyError::UnknownOverrideId { id: "gotos".to_string() }]);
}

#[test]
fn strictness_runs_allow_restrict_trusted_only_ban() {
    use Decision::*;
    let order = [Allow, Restrict, TrustedOnly, Ban];
    for (i, a) in order.iter().enumerate() {
        for (j, b) in order.iter().enumerate() {
            // is_looser(new, old): the new decision is looser than the old one
            assert_eq!(is_looser(*a, *b), i < j, "is_looser({:?}, {:?})", a, b);
        }
    }
}

// ------------------------------------------------------------------- findings

#[test]
fn a_finding_maps_to_the_rule_that_enabled_its_check() {
    let p = policy(vec![
        rule("goto", Decision::Ban, &["cppcoreguidelines-avoid-goto"]),
        rule("c_style_casts", Decision::Ban, &["google-readability-casting"]),
    ]);
    assert_eq!(rule_for_check(&p, &"google-readability-casting".to_string()), Some(1));
}

#[test]
fn a_finding_from_a_dormant_check_maps_to_nothing() {
    let p = policy(vec![rule("variable_index", Decision::Allow, &["cppcoreguidelines-pro-bounds-constant-array-index"])]);
    assert_eq!(rule_for_check(&p, &"cppcoreguidelines-pro-bounds-constant-array-index".to_string()), None);
}

#[test]
fn a_finding_from_an_unknown_check_maps_to_nothing() {
    assert_eq!(rule_for_check(&base(), &"clang-diagnostic-error".to_string()), None);
}

#[test]
fn in_a_verified_function_every_finding_stands() {
    for d in [Decision::Ban, Decision::Restrict, Decision::TrustedOnly] {
        assert!(keep_finding(d, Kind::Verified), "{:?} in verified", d);
    }
}

#[test]
fn in_a_trusted_function_only_trusted_only_findings_are_dropped() {
    assert!(keep_finding(Decision::Ban, Kind::Trusted));
    assert!(keep_finding(Decision::Restrict, Kind::Trusted));
    assert!(!keep_finding(Decision::TrustedOnly, Kind::Trusted));
}

#[test]
fn in_a_plain_function_nothing_is_reported() {
    for d in [Decision::Ban, Decision::Restrict, Decision::TrustedOnly] {
        assert!(!keep_finding(d, Kind::Plain), "{:?} in plain", d);
    }
}
