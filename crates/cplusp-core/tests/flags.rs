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
        "-ffast-math",
        "-Ofast",
        "-funsafe-math-optimizations",
        "-ffinite-math-only",
        "-fassociative-math",
        "-freciprocal-math",
        "-fno-signed-zeros",
        "-fno-honor-nans",
        "-fno-honor-infinities",
        "-ffp-model=fast",
        "-mfpmath=387",
        "-m32",
        "-fdenormal-fp-math=preserve-sign",
        "-ffp-eval-method=extended",
    ] {
        assert_eq!(check(&["-std=c++23", "-ffp-contract=off", f], &[]), (vec![(2, FlagFault::Float)], false, false), "{f}");
    }
    assert_eq!(
        check(&["-std=c++23", "-ffp-contract=off", "-fdenormal-fp-math=ieee", "-ffp-eval-method=source"], &[]),
        (vec![], false, false)
    );
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
    for f in [
        "-E",
        "-P",
        "-M",
        "-MM",
        "-MV",
        "-dM",
        "-dD",
        "-dI",
        "-###",
        "-fdriver-only",
        "-Xpreprocessor",
        "-Xclang",
        "-include-pch",
        "-Wp,-MD",
        "-fmodules",
        "-MJ",
        "-MJx.json",
    ] {
        assert_eq!(check(&["-std=c++23", "-ffp-contract=off", f], &[]), (vec![(2, FlagFault::Reads)], false, false), "{f}");
    }
}

#[test]
fn response_files_config_files_and_hidden_warnings_are_refused() {
    assert_eq!(check(&["-std=c++23", "-ffp-contract=off", "@args.txt"], &[]), (vec![(2, FlagFault::ResponseFile)], false, false));
    assert_eq!(
        check(&["-std=c++23", "-ffp-contract=off", "--config", "--config=x.cfg"], &[]),
        (vec![(2, FlagFault::ConfigFile), (3, FlagFault::ConfigFile)], false, false)
    );
    assert_eq!(
        check(&["-std=c++23", "-ffp-contract=off", "-w", "-Wno-everything", "--no-warnings"], &[]),
        (vec![(2, FlagFault::HidesAll), (3, FlagFault::HidesAll), (4, FlagFault::HidesAll)], false, false)
    );
    let checks = ["clang-diagnostic-shadow", "readability-x"];
    assert_eq!(
        check(&["-std=c++23", "-ffp-contract=off", "-Wno-shadow", "-Wno-unused"], &checks),
        (vec![(2, FlagFault::HidesRow)], false, false)
    );
    // The match needs the prefix: a check named `shadow` alone, or with another prefix, is no warning of the policy.
    assert_eq!(
        check(&["-std=c++23", "-ffp-contract=off", "-Wno-shadow"], &["shadow", "other-clang-diagnostic-shadow"]),
        (vec![], false, false)
    );
}

#[test]
fn the_first_reason_of_a_flag_wins() {
    // `-ffp-contract=fast` is both a contraction flag and the last one: one fault, Float.
    assert_eq!(check(&["-std=c++23", "-ffp-contract=fast"], &[]), (vec![(1, FlagFault::Float)], false, true));
}

/// `--std VALUE` in two words sets the standard too, under a `-std=c++23` that the gate sees. The gate cannot read the value, so it
/// refuses the bare flag, decision 0129.
#[test]
fn the_bare_std_flag_is_refused() {
    assert_eq!(check(&["-std=c++23", "-ffp-contract=off", "--std", "c++20"], &[]), (vec![(2, FlagFault::Std)], false, false));
}

/// `-ansi` and `--ansi` set C++98, so the gate refuses them as a standard before C++23, decision 0130.
#[test]
fn ansi_is_a_standard_before_cxx23() {
    assert_eq!(
        check(&["-std=c++23", "-ffp-contract=off", "-ansi", "--ansi"], &[]),
        (vec![(2, FlagFault::Std), (3, FlagFault::Std)], false, false)
    );
}

/// A flag with a separate value takes the next flag as its value. The gate refuses it when that next flag looks like a flag,
/// decision 0130. A lone `-` and a plain word are values.
#[test]
fn a_flag_that_would_swallow_the_next_flag_is_refused() {
    for f in [
        "-I",
        "-isystem",
        "-idirafter",
        "-iquote",
        "-include",
        "-imacros",
        "-D",
        "-U",
        "-x",
        "-o",
        "-MF",
        "-MT",
        "-MQ",
        "-target",
        "-isysroot",
        "-cxx-isystem",
        "-isystem-after",
    ] {
        assert_eq!(check(&[f, "-std=c++23", "-ffp-contract=off"], &[]), (vec![(0, FlagFault::Swallows)], false, false), "{f}");
    }
    // More flags that take a value, decision 0135.
    for f in [
        "-F",
        "-L",
        "-l",
        "-B",
        "-z",
        "-u",
        "-e",
        "-T",
        "-rpath",
        "-arch",
        "-dumpdir",
        "-Xlinker",
        "-Xassembler",
        "-Xanalyzer",
        "-Xarch_host",
        "-Xarch_device",
        "-mllvm",
        "-iprefix",
        "-iwithprefix",
        "-iwithprefixbefore",
        "-iframework",
        "-iwithsysroot",
        "-ivfsoverlay",
        "-stdlib++-isystem",
        "--sysroot",
        "-working-directory",
        "-module-dependency-dir",
        "-resource-dir",
        "-fdebug-compilation-dir",
        "-serialize-diagnostics",
        "--serialize-diagnostics",
        "--param",
        "--language",
        "--output",
        "--include-directory",
        "--define-macro",
        "--undefine-macro",
        "--include",
        "--imacros",
        "--prefix",
        "--system-header-prefix",
        "--library-directory",
    ] {
        assert_eq!(check(&[f, "-std=c++23", "-ffp-contract=off"], &[]), (vec![(0, FlagFault::Swallows)], false, false), "{f}");
        assert_eq!(check(&["-std=c++23", "-ffp-contract=off", f], &[]), (vec![(2, FlagFault::Swallows)], false, false), "{f}");
    }
    // Each is an exact match: a joined value is no flag that takes the next one.
    assert_eq!(check(&["-std=c++23", "-ffp-contract=off", "-Llib", "-lm", "-F.", "--sysroot=/"], &[]), (vec![], false, false));
    // `-Xclang` keeps its own reason, which comes first. The flag that it swallows is judged too.
    assert_eq!(
        check(&["-Xclang", "-std=c++20", "-std=c++23", "-ffp-contract=off"], &[]),
        (vec![(0, FlagFault::Reads), (1, FlagFault::Std)], false, false)
    );
    // A value is fine, and so is a lone `-`.
    assert_eq!(check(&["-I", "include", "-o", "-", "-std=c++23", "-ffp-contract=off"], &[]), (vec![], false, false));
    // A flag at the end takes the first flag of the gate as its value, decision 0134.
    for f in ["-I", "-x", "-D", "-o"] {
        assert_eq!(check(&["-std=c++23", "-ffp-contract=off", f], &[]), (vec![(2, FlagFault::Swallows)], false, false), "{f}");
    }
}

/// A target of 32-bit x86 computes a double with the x87 unit, so it is refused as a change of floating point, and a 64-bit
/// target is fine, decision 0151.
#[test]
fn a_32_bit_x86_target_is_refused() {
    for t in ["--target=i686-linux-gnu", "--target=i386-pc-linux", "--target=i486-unknown-linux", "--target=i586-linux", "-m16"] {
        assert_eq!(check(&["-std=c++23", "-ffp-contract=off", t], &[]), (vec![(2, FlagFault::Float)], false, false), "{t}");
    }
    for f in ["-target", "-arch"] {
        assert_eq!(
            check(&["-std=c++23", "-ffp-contract=off", f, "i686-linux-gnu"], &[]),
            (vec![(2, FlagFault::Float)], false, false),
            "{f}"
        );
        assert_eq!(check(&["-std=c++23", "-ffp-contract=off", f, "x86_64-linux-gnu"], &[]), (vec![], false, false), "{f}");
    }
    assert_eq!(
        check(&["-std=c++23", "-ffp-contract=off", "--target=x86_64-linux-gnu", "--target=aarch64-linux-gnu"], &[]),
        (vec![], false, false)
    );
}

/// More ways to a double in the x87 unit: the names i786 to i986, and flags that turn SSE off, decision 0152.
#[test]
fn more_ways_to_an_x87_double_are_refused() {
    for t in ["--target=i786-linux-gnu", "--target=i886-pc-linux", "--target=i986-linux", "-mno-sse", "-mno-sse2", "-mgeneral-regs-only"] {
        assert_eq!(check(&["-std=c++23", "-ffp-contract=off", t], &[]), (vec![(2, FlagFault::Float)], false, false), "{t}");
    }
    assert_eq!(check(&["-std=c++23", "-ffp-contract=off", "-target", "i986-linux-gnu"], &[]), (vec![(2, FlagFault::Float)], false, false));
    // Not a 32-bit x86: no digit, a digit below 3, or no 86 after it.
    for t in ["--target=i86-linux", "--target=i286-linux", "--target=i7-linux", "-msoft-float", "-mx32"] {
        assert_eq!(check(&["-std=c++23", "-ffp-contract=off", t], &[]), (vec![], false, false), "{t}");
    }
}
