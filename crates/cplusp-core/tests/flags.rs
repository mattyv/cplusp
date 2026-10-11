//! The flags of the compiler that the gate refuses, decisions 0022 and 0128. Each test gives the flags after `--` and reads the
//! faults by the index of each flag.

use cplusp_core::flags::*;

fn check(flags: &[&str], checks: &[&str]) -> (Vec<(usize, FlagFault)>, bool, bool) {
    let f: Vec<Vec<u8>> = flags.iter().map(|s| s.as_bytes().to_vec()).collect();
    let c: Vec<Vec<u8>> = checks.iter().map(|s| s.as_bytes().to_vec()).collect();
    let r = check_flags(&f, &c);
    (r.faults, r.no_std, r.no_contract_off)
}

const GOOD: [&str; 2] = ["-std=c++23", "-ffp-contract=off"];

#[test]
fn the_two_flags_the_gate_needs_pass() {
    assert_eq!(check(&GOOD, &[]), (vec![], false, false));
    assert_eq!(check(&["--std=gnu++2c", "-ffp-model=strict", "-O2", "-Iinclude"], &[]), (vec![], false, false));
}

#[test]
fn a_missing_std_or_contraction_flag_is_named() {
    assert_eq!(check(&["-ffp-contract=off"], &[]), (vec![], true, false));
    assert_eq!(check(&["-std=c++23"], &[]), (vec![], false, true));
    assert_eq!(check(&[], &[]), (vec![], true, true));
}

#[test]
fn each_flag_that_changes_floating_point_is_refused() {
    for f in [
        "-ffast-math", "-Ofast", "-funsafe-math-optimizations", "-ffinite-math-only", "-fassociative-math", "-freciprocal-math", "-fno-signed-zeros",
        "-fno-honor-nans", "-fno-honor-infinities", "-ffp-model=fast", "-mfpmath=387", "-m32", "-fdenormal-fp-math=preserve-sign",
        "-ffp-eval-method=extended",
    ] {
        assert_eq!(check(&["-std=c++23", "-ffp-contract=off", f], &[]), (vec![(2, FlagFault::Float)], false, false), "{f}");
    }
    assert_eq!(check(&["-std=c++23", "-ffp-contract=off", "-fdenormal-fp-math=ieee", "-ffp-eval-method=source"], &[]), (vec![], false, false));
}

#[test]
fn only_the_last_contraction_flag_counts() {
    // The last flag that sets contraction wins. An earlier off does not save a later on.
    assert_eq!(check(&["-std=c++23", "-ffp-contract=off", "-ffp-contract=fast"], &[]), (vec![(2, FlagFault::Float)], false, false));
    assert_eq!(check(&["-std=c++23", "-ffp-contract=fast", "-ffp-contract=off"], &[]), (vec![], false, false));
    assert_eq!(check(&["-std=c++23", "-ffp-contract=off", "-ffp-model=precise"], &[]), (vec![(2, FlagFault::Float)], false, false));
    // An on with no off anywhere is refused, and the off is still missing.
    assert_eq!(check(&["-std=c++23", "-ffp-contract=on"], &[]), (vec![(1, FlagFault::Float)], false, true));
}

#[test]
fn a_std_before_cxx23_is_refused() {
    assert_eq!(check(&["-std=c++20", "-ffp-contract=off"], &[]), (vec![(0, FlagFault::Std)], false, false));
    assert_eq!(check(&["-std=c++23", "-ffp-contract=off", "--std=c++17"], &[]), (vec![(2, FlagFault::Std)], false, false));
}

#[test]
fn flags_that_change_what_the_compiler_reads_or_reports_are_refused() {
    for f in ["-E", "-P", "-M", "-MM", "-MV", "-dM", "-dD", "-dI", "-###", "-fdriver-only", "-Xpreprocessor", "-Xclang", "-include-pch", "-Wp,-MD", "-fmodules"] {
        assert_eq!(check(&["-std=c++23", "-ffp-contract=off", f], &[]), (vec![(2, FlagFault::Reads)], false, false), "{f}");
    }
}

#[test]
fn response_files_config_files_and_hidden_warnings_are_refused() {
    assert_eq!(check(&["-std=c++23", "-ffp-contract=off", "@args.txt"], &[]), (vec![(2, FlagFault::ResponseFile)], false, false));
    assert_eq!(check(&["-std=c++23", "-ffp-contract=off", "--config", "--config=x.cfg"], &[]), (vec![(2, FlagFault::ConfigFile), (3, FlagFault::ConfigFile)], false, false));
    assert_eq!(check(&["-std=c++23", "-ffp-contract=off", "-w", "-Wno-everything"], &[]), (vec![(2, FlagFault::HidesAll), (3, FlagFault::HidesAll)], false, false));
    let checks = ["clang-diagnostic-shadow", "readability-x"];
    assert_eq!(check(&["-std=c++23", "-ffp-contract=off", "-Wno-shadow", "-Wno-unused"], &checks), (vec![(2, FlagFault::HidesRow)], false, false));
}

#[test]
fn the_first_reason_of_a_flag_wins() {
    // `-ffp-contract=fast` is both a contraction flag and the last one: one fault, Float.
    assert_eq!(check(&["-std=c++23", "-ffp-contract=fast"], &[]), (vec![(1, FlagFault::Float)], false, true));
}
