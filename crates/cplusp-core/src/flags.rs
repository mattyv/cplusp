//! The flags of the compiler that the gate refuses, decisions 0022, 0128, 0129, 0130, 0134 and 0135. The shell gives each flag after `--` as bytes, and the
//! checks of the config. The core gives the index and the reason of each refused flag, and says when a flag that the gate needs is
//! missing. It proves the facts of a run with no refusal, `check_flags`.

use vstd::prelude::*;

verus! {

/// Why the gate refuses a flag. `Float` changes floating-point results. `Std` names a standard before C++23, or is the bare `--std`. `Reads` changes what
/// the compiler reads or reports. `HidesAll` hides each warning, and `HidesRow` a warning that the policy names. `Swallows` takes the next flag as its value, or stands at the end and takes the first flag of the gate.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum FlagFault {
    Float,
    Std,
    Reads,
    ResponseFile,
    ConfigFile,
    HidesAll,
    HidesRow,
    Swallows,
}

pub struct FlagCheck {
    pub faults: Vec<(usize, FlagFault)>,
    pub no_std: bool,
    pub no_contract_off: bool,
}

// ------------------------------------------------------------------ the rules

pub open spec fn starts(f: Seq<u8>, p: Seq<u8>) -> bool {
    p.len() <= f.len() && f.subrange(0, p.len() as int) == p
}

pub open spec fn rest(f: Seq<u8>, p: Seq<u8>) -> Seq<u8> {
    f.subrange(p.len() as int, f.len() as int)
}

/// What a flag sets contraction to. `-ffp-model=precise` is `on` and `-ffp-model=strict` is `off`.
pub open spec fn contraction(f: Seq<u8>) -> Option<Seq<u8>> {
    if f == b"-ffp-model=precise"@ {
        Some(b"on"@)
    } else if f == b"-ffp-model=strict"@ {
        Some(b"off"@)
    } else if starts(f, b"-ffp-contract="@) {
        Some(rest(f, b"-ffp-contract="@))
    } else {
        None
    }
}

pub open spec fn is_off(f: Seq<u8>) -> bool {
    contraction(f) == Some(b"off"@)
}

/// The value of `-std=X` or `--std=X`.
pub open spec fn std_value(f: Seq<u8>) -> Option<Seq<u8>> {
    if starts(f, b"-std="@) {
        Some(rest(f, b"-std="@))
    } else if starts(f, b"--std="@) {
        Some(rest(f, b"--std="@))
    } else {
        None
    }
}

/// A standard at C++23 or later.
pub open spec fn std_ok(v: Seq<u8>) -> bool {
    v == b"c++23"@ || v == b"c++2b"@ || v == b"c++26"@ || v == b"c++2c"@ || v == b"gnu++23"@ || v == b"gnu++2b"@ || v == b"gnu++26"@
        || v == b"gnu++2c"@
}

pub open spec fn float_flag(f: Seq<u8>) -> bool {
    f == b"-ffast-math"@ || f == b"-Ofast"@ || f == b"-funsafe-math-optimizations"@ || f == b"-ffinite-math-only"@ || f
        == b"-fassociative-math"@ || f == b"-freciprocal-math"@ || f == b"-fno-signed-zeros"@ || f == b"-fno-honor-nans"@ || f
        == b"-fno-honor-infinities"@ || f == b"-ffp-model=fast"@ || f == b"-mfpmath=387"@ || f == b"-m32"@ || f
        == b"-mno-sse"@ || f == b"-mno-sse2"@ || f == b"-mgeneral-regs-only"@
}

/// A triple of 32-bit x86, which computes a double with the x87 unit: `i`, a digit from 3 to 9, then `86`, decisions 0151 and 0152.
pub open spec fn x87_triple(v: Seq<u8>) -> bool {
    v.len() >= 4 && v[0] == 0x69 && 0x33 <= v[1] <= 0x39 && v[2] == 0x38 && v[3] == 0x36
}

/// The flag at `i` gives a 32-bit x86 build: `-m16`, `--target=X`, or `-target X` and `-arch X` with `X` the next flag, decision 0151.
pub open spec fn x87_at(fl: Seq<Vec<u8>>, i: int) -> bool {
    let f = fl[i]@;
    f == b"-m16"@ || (starts(f, b"--target="@) && x87_triple(rest(f, b"--target="@))) || ((f == b"-target"@ || f == b"-arch"@) && i + 1
        < fl.len() && x87_triple(fl[i + 1]@))
}

pub open spec fn reads(f: Seq<u8>) -> bool {
    f == b"-E"@ || f == b"-P"@ || f == b"-M"@ || f == b"-MM"@ || f == b"-MV"@ || f == b"-dM"@ || f == b"-dD"@ || f == b"-dI"@ || f
        == b"-###"@ || f == b"-fdriver-only"@ || f == b"-Xpreprocessor"@ || f == b"-Xclang"@ || f == b"-include-pch"@ || starts(
        f,
        b"-Wp,"@,
    ) || starts(f, b"-fmodule"@) || starts(f, b"-MJ"@)
}

/// `-ansi` and `--ansi` set C++98, decision 0130.
pub open spec fn is_ansi(f: Seq<u8>) -> bool {
    f == b"-ansi"@ || f == b"--ansi"@
}

/// A flag whose value is the next flag, decision 0130.
pub open spec fn takes_value(f: Seq<u8>) -> bool {
    f == b"-I"@ || f == b"-isystem"@ || f == b"-idirafter"@ || f == b"-iquote"@ || f == b"-include"@ || f == b"-imacros"@ || f == b"-D"@ || f
        == b"-U"@ || f == b"-x"@ || f == b"-o"@ || f == b"-MF"@ || f == b"-MT"@ || f == b"-MQ"@ || f == b"-Xclang"@ || f == b"-Xpreprocessor"@
        || f == b"-target"@ || f == b"-isysroot"@ || f == b"-cxx-isystem"@ || f == b"-isystem-after"@ || takes_value_more(f)
}

/// More flags whose value is the next flag, decision 0135. A list of its own keeps `takes_value` short enough to read.
pub open spec fn takes_value_more(f: Seq<u8>) -> bool {
    f == b"-F"@ || f == b"-L"@ || f == b"-l"@ || f == b"-B"@ || f == b"-z"@ || f == b"-u"@ || f == b"-e"@ || f == b"-T"@ || f == b"-rpath"@ || f == b"-arch"@ || f == b"-dumpdir"@ || f == b"-Xlinker"@ || f == b"-Xassembler"@ || f == b"-Xanalyzer"@ || f == b"-Xarch_host"@ || f == b"-Xarch_device"@ || f == b"-mllvm"@ || f == b"-iprefix"@ || f == b"-iwithprefix"@ || f == b"-iwithprefixbefore"@ || f == b"-iframework"@ || f == b"-iwithsysroot"@ || f == b"-ivfsoverlay"@ || f == b"-stdlib++-isystem"@ || f == b"--sysroot"@ || f == b"-working-directory"@ || f == b"-module-dependency-dir"@ || f == b"-resource-dir"@ || f == b"-fdebug-compilation-dir"@ || f == b"-serialize-diagnostics"@ || f == b"--serialize-diagnostics"@ || f == b"--param"@ || f == b"--language"@ || f == b"--output"@ || f == b"--include-directory"@ || f == b"--define-macro"@ || f == b"--undefine-macro"@ || f == b"--include"@ || f == b"--imacros"@ || f == b"--prefix"@ || f == b"--system-header-prefix"@ || f == b"--library-directory"@
}

/// The flag at `i` takes as its value a next flag that starts with `-`. A lone `-` is a value. At the end, it takes the first flag
/// that the gate adds, decision 0134.
pub open spec fn swallows(fl: Seq<Vec<u8>>, i: int) -> bool {
    takes_value(fl[i]@) && (i + 1 == fl.len() || (fl[i + 1]@.len() > 1 && fl[i + 1]@[0] == 0x2d))
}

/// A check of the config is the compiler warning `name`.
pub open spec fn names_warning(cs: Seq<Vec<u8>>, name: Seq<u8>) -> bool {
    exists|k: int| 0 <= k < cs.len() && #[trigger] cs[k]@ == b"clang-diagnostic-"@ + name
}

/// The index of the last flag that sets contraction: the one the compiler follows.
pub open spec fn last_contract(fl: Seq<Vec<u8>>, n: int) -> Option<int>
    decreases n,
{
    if n <= 0 {
        None
    } else if contraction(fl[n - 1]@) is Some {
        Some(n - 1)
    } else {
        last_contract(fl, n - 1)
    }
}

/// The reason to refuse the flag at `i`, in the order of decision 0128, or none.
pub open spec fn fault(fl: Seq<Vec<u8>>, cs: Seq<Vec<u8>>, i: int) -> Option<FlagFault> {
    let f = fl[i]@;
    let contracts = last_contract(fl, fl.len() as int) == Some(i) && !is_off(f);
    let denormals = starts(f, b"-fdenormal-fp-math="@) && f != b"-fdenormal-fp-math=ieee"@;
    let eval = starts(f, b"-ffp-eval-method="@) && f != b"-ffp-eval-method=source"@;
    if contracts || denormals || eval || float_flag(f) || x87_at(fl, i) {
        Some(FlagFault::Float)
    } else if f == b"--std"@ || is_ansi(f) || (std_value(f) is Some && !std_ok(std_value(f).unwrap())) {
        Some(FlagFault::Std)
    } else if reads(f) {
        Some(FlagFault::Reads)
    } else if starts(f, b"@"@) {
        Some(FlagFault::ResponseFile)
    } else if f == b"--config"@ || starts(f, b"--config="@) {
        Some(FlagFault::ConfigFile)
    } else if f == b"-w"@ || f == b"-Wno-everything"@ || f == b"--no-warnings"@ {
        Some(FlagFault::HidesAll)
    } else if starts(f, b"-Wno-"@) && names_warning(cs, rest(f, b"-Wno-"@)) {
        Some(FlagFault::HidesRow)
    } else if swallows(fl, i) {
        Some(FlagFault::Swallows)
    } else {
        None
    }
}

/// The faults of the first `n` flags, in order.
pub open spec fn faults(fl: Seq<Vec<u8>>, cs: Seq<Vec<u8>>, n: int) -> Seq<(usize, FlagFault)>
    decreases n,
{
    if n <= 0 {
        Seq::empty()
    } else {
        match fault(fl, cs, n - 1) {
            Some(k) => faults(fl, cs, n - 1).push(((n - 1) as usize, k)),
            None => faults(fl, cs, n - 1),
        }
    }
}

proof fn lemma_faults_empty(fl: Seq<Vec<u8>>, cs: Seq<Vec<u8>>, n: int)
    requires
        0 <= n <= fl.len(),
    ensures
        faults(fl, cs, n).len() == 0 <==> forall|i: int| 0 <= i < n ==> #[trigger] fault(fl, cs, i) is None,
    decreases n,
{
    if n > 0 {
        lemma_faults_empty(fl, cs, n - 1);
    }
}

proof fn lemma_last_contract(fl: Seq<Vec<u8>>, n: int)
    requires
        0 <= n <= fl.len(),
    ensures
        last_contract(fl, n) matches Some(j) ==> 0 <= j < n && contraction(fl[j]@) is Some,
        (exists|i: int| 0 <= i < n && #[trigger] contraction(fl[i]@) is Some) ==> last_contract(fl, n) is Some,
    decreases n,
{
    if n > 0 {
        lemma_last_contract(fl, n - 1);
        if contraction(fl[n - 1]@) is None {
            assert forall|i: int| 0 <= i < n && #[trigger] contraction(fl[i]@) is Some implies i < n - 1 by {}
        }
    }
}

/// A run with no refusal, decision 0128: a `-std` flag, each `-std` at C++23 or later, the last contraction off, and no flag that
/// changes floating point, changes what the compiler reads or reports, or hides a warning of the policy. No flag takes the next flag,
/// or the first flag of the gate, as its value.
pub open spec fn clean(fl: Seq<Vec<u8>>, cs: Seq<Vec<u8>>) -> bool {
    &&& exists|i: int| 0 <= i < fl.len() && #[trigger] std_value(fl[i]@) is Some
    &&& forall|i: int| 0 <= i < fl.len() && #[trigger] std_value(fl[i]@) is Some ==> std_ok(std_value(fl[i]@).unwrap())
    &&& last_contract(fl, fl.len() as int) matches Some(j) && is_off(fl[j]@)
    &&& forall|i: int| 0 <= i < fl.len() ==> flag_clean(#[trigger] fl[i]@, cs)
    &&& forall|i: int| 0 <= i < fl.len() ==> !#[trigger] swallows(fl, i)
    &&& forall|i: int| 0 <= i < fl.len() ==> !#[trigger] x87_at(fl, i)
}

/// One flag that changes no floating-point result, nothing that the compiler reads or reports, and no warning of the policy. It
/// names no file of flags, and it is no bare `--std`, decision 0129.
pub open spec fn flag_clean(f: Seq<u8>, cs: Seq<Vec<u8>>) -> bool {
    &&& !float_flag(f)
    &&& !(starts(f, b"-fdenormal-fp-math="@) && f != b"-fdenormal-fp-math=ieee"@)
    &&& !(starts(f, b"-ffp-eval-method="@) && f != b"-ffp-eval-method=source"@)
    &&& !reads(f)
    &&& !starts(f, b"@"@)
    &&& f != b"--config"@ && !starts(f, b"--config="@)
    &&& f != b"-w"@ && f != b"-Wno-everything"@ && f != b"--no-warnings"@
    &&& f != b"--std"@ && !is_ansi(f)
    &&& !(starts(f, b"-Wno-"@) && names_warning(cs, rest(f, b"-Wno-"@)))
}

// ------------------------------------------------------------------ the code

fn eq(f: &Vec<u8>, w: &[u8]) -> (r: bool)
    ensures
        r == (f@ == w@),
{
    if f.len() != w.len() {
        return false;
    }
    let mut i = 0;
    while i < w.len()
        invariant
            i <= w.len(),
            f.len() == w.len(),
            forall|j: int| 0 <= j < i ==> f@[j] == w@[j],
        decreases w.len() - i,
    {
        if f[i] != w[i] {
            return false;
        }
        i += 1;
    }
    proof {
        assert(f@ =~= w@);
    }
    true
}

fn starts_exec(f: &Vec<u8>, p: &[u8]) -> (r: bool)
    ensures
        r == starts(f@, p@),
{
    if p.len() > f.len() {
        return false;
    }
    let mut i = 0;
    while i < p.len()
        invariant
            i <= p.len() <= f.len(),
            forall|j: int| 0 <= j < i ==> f@[j] == p@[j],
        decreases p.len() - i,
    {
        if f[i] != p[i] {
            proof {
                assert(f@.subrange(0, p.len() as int)[i as int] != p@[i as int]);
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert(f@.subrange(0, p.len() as int) =~= p@);
    }
    true
}

/// `f` from the place `at` equals `w`.
fn rest_is(f: &Vec<u8>, at: usize, w: &[u8]) -> (r: bool)
    requires
        at <= f.len(),
    ensures
        r == (f@.subrange(at as int, f.len() as int) == w@),
{
    if f.len() - at != w.len() {
        proof {
            if f@.subrange(at as int, f.len() as int) == w@ {
                assert(f@.subrange(at as int, f.len() as int).len() == w@.len());
            }
        }
        return false;
    }
    let mut i = 0;
    while i < w.len()
        invariant
            i <= w.len(),
            at + w.len() == f.len(),
            forall|j: int| 0 <= j < i ==> f@[at + j] == w@[j],
        decreases w.len() - i,
    {
        if f[at + i] != w[i] {
            proof {
                assert(f@.subrange(at as int, f.len() as int)[i as int] != w@[i as int]);
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert(f@.subrange(at as int, f.len() as int) =~= w@);
    }
    true
}

/// What the flag sets contraction to: 0 for none, 1 for off, 2 for any other value.
fn contraction_exec(f: &Vec<u8>) -> (r: u8)
    ensures
        r == 0 <==> contraction(f@) is None,
        r == 1 <==> is_off(f@),
{
    if eq(f, b"-ffp-model=precise") {
        proof {
            assert(b"on"@ != b"off"@) by {
                assert(b"on"@.len() != b"off"@.len());
            }
        }
        2
    } else if eq(f, b"-ffp-model=strict") {
        1
    } else if starts_exec(f, b"-ffp-contract=") {
        if rest_is(f, 14, b"off") {
            1
        } else {
            2
        }
    } else {
        0
    }
}

fn std_ok_exec(f: &Vec<u8>, at: usize) -> (r: bool)
    requires
        at <= f.len(),
    ensures
        r == std_ok(f@.subrange(at as int, f.len() as int)),
{
    rest_is(f, at, b"c++23") || rest_is(f, at, b"c++2b") || rest_is(f, at, b"c++26") || rest_is(f, at, b"c++2c") || rest_is(f, at, b"gnu++23")
        || rest_is(f, at, b"gnu++2b") || rest_is(f, at, b"gnu++26") || rest_is(f, at, b"gnu++2c")
}

/// The flag sets `-std`, and whether its value is at C++23 or later.
fn std_exec(f: &Vec<u8>) -> (r: Option<bool>)
    ensures
        match r {
            None => std_value(f@) is None,
            Some(ok) => std_value(f@) is Some && ok == std_ok(std_value(f@).unwrap()),
        },
{
    if starts_exec(f, b"-std=") {
        Some(std_ok_exec(f, 5))
    } else if starts_exec(f, b"--std=") {
        Some(std_ok_exec(f, 6))
    } else {
        None
    }
}

fn float_exec(f: &Vec<u8>) -> (r: bool)
    ensures
        r == float_flag(f@),
{
    eq(f, b"-ffast-math") || eq(f, b"-Ofast") || eq(f, b"-funsafe-math-optimizations") || eq(f, b"-ffinite-math-only") || eq(f, b"-fassociative-math")
        || eq(f, b"-freciprocal-math") || eq(f, b"-fno-signed-zeros") || eq(f, b"-fno-honor-nans") || eq(f, b"-fno-honor-infinities") || eq(
        f,
        b"-ffp-model=fast",
    ) || eq(f, b"-mfpmath=387") || eq(f, b"-m32") || eq(f, b"-mno-sse") || eq(f, b"-mno-sse2") || eq(f, b"-mgeneral-regs-only")
}

/// The bytes of `v` from `from` are a triple of 32-bit x86.
fn x87_triple_exec(v: &Vec<u8>, from: usize) -> (r: bool)
    requires
        from <= v.len(),
    ensures
        r == x87_triple(v@.subrange(from as int, v.len() as int)),
{
    v.len() - from >= 4 && v[from] == 0x69 && 0x33 <= v[from + 1] && v[from + 1] <= 0x39 && v[from + 2] == 0x38 && v[from + 3] == 0x36
}

fn x87_exec(fl: &Vec<Vec<u8>>, i: usize) -> (r: bool)
    requires
        i < fl.len(),
    ensures
        r == x87_at(fl@, i as int),
{
    let f = &fl[i];
    proof {
        assert(fl@[i as int]@.subrange(0, fl@[i as int]@.len() as int) =~= fl@[i as int]@);
        if i + 1 < fl.len() {
            assert(fl@[i + 1]@.subrange(0, fl@[i + 1]@.len() as int) =~= fl@[i + 1]@);
        }
    }
    eq(f, b"-m16") || (starts_exec(f, b"--target=") && x87_triple_exec(f, 9)) || ((eq(f, b"-target") || eq(f, b"-arch")) && i + 1
        < fl.len() && x87_triple_exec(&fl[i + 1], 0))
}

fn reads_exec(f: &Vec<u8>) -> (r: bool)
    ensures
        r == reads(f@),
{
    eq(f, b"-E") || eq(f, b"-P") || eq(f, b"-M") || eq(f, b"-MM") || eq(f, b"-MV") || eq(f, b"-dM") || eq(f, b"-dD") || eq(f, b"-dI") || eq(
        f,
        b"-###",
    ) || eq(f, b"-fdriver-only") || eq(f, b"-Xpreprocessor") || eq(f, b"-Xclang") || eq(f, b"-include-pch") || starts_exec(f, b"-Wp,")
        || starts_exec(f, b"-fmodule") || starts_exec(f, b"-MJ")
}

/// The bytes of `c` after 17 equal the bytes of `f` after 5.
fn tail_eq(c: &Vec<u8>, f: &Vec<u8>) -> (r: bool)
    requires
        c.len() >= 17,
        f.len() >= 5,
        c.len() - 17 == f.len() - 5,
    ensures
        r == (forall|j: int| 0 <= j < f.len() - 5 ==> #[trigger] c@[17 + j] == f@[5 + j]),
{
    let mut i = 0;
    while i < f.len() - 5
        invariant
            i <= f.len() - 5,
            c.len() >= 17,
            f.len() >= 5,
            c.len() - 17 == f.len() - 5,
            forall|j: int| 0 <= j < i ==> #[trigger] c@[17 + j] == f@[5 + j],
        decreases f.len() - 5 - i,
    {
        if c[17 + i] != f[5 + i] {
            return false;
        }
        i += 1;
    }
    true
}

/// A check of the config is `clang-diagnostic-` and the rest of the flag after `-Wno-`.
fn names_warning_exec(cs: &Vec<Vec<u8>>, f: &Vec<u8>) -> (r: bool)
    requires
        starts(f@, b"-Wno-"@),
    ensures
        r == names_warning(cs@, rest(f@, b"-Wno-"@)),
{
    let mut k = 0;
    while k < cs.len()
        invariant
            k <= cs.len(),
            starts(f@, b"-Wno-"@),
            forall|j: int| 0 <= j < k ==> #[trigger] cs@[j]@ != b"clang-diagnostic-"@ + rest(f@, b"-Wno-"@),
        decreases cs.len() - k,
    {
        let c = &cs[k];
        let p: &[u8] = b"clang-diagnostic-";
        let mut ok = false;
        if c.len() >= 17 && f.len() >= 5 && c.len() - 17 == f.len() - 5 && starts_exec(c, p) {
            ok = tail_eq(c, f);
        }
        proof {
            let want = b"clang-diagnostic-"@ + rest(f@, b"-Wno-"@);
            assert(p@ == b"clang-diagnostic-"@);
            assert(want.len() == 17 + f.len() - 5);
            if ok {
                assert forall|m: int| 0 <= m < c@.len() implies #[trigger] c@[m] == want[m] by {
                    if m < 17 {
                        assert(c@.subrange(0, 17)[m] == p@[m]);
                    } else {
                        assert(c@[17 + (m - 17)] == f@[5 + (m - 17)]);
                    }
                }
                assert(c@ =~= want);
            } else if c@ == want {
                assert(c@.len() == want.len());
                assert(c@.subrange(0, 17) =~= b"clang-diagnostic-"@);
                assert forall|j: int| 0 <= j < f.len() - 5 implies #[trigger] c@[17 + j] == f@[5 + j] by {
                    assert(c@[17 + j] == want[17 + j]);
                }
            }
        }
        if ok {
            return true;
        }
        k += 1;
    }
    false
}

fn takes_value_exec(f: &Vec<u8>) -> (r: bool)
    ensures
        r == takes_value(f@),
{
    eq(f, b"-I") || eq(f, b"-isystem") || eq(f, b"-idirafter") || eq(f, b"-iquote") || eq(f, b"-include") || eq(f, b"-imacros") || eq(f, b"-D")
        || eq(f, b"-U") || eq(f, b"-x") || eq(f, b"-o") || eq(f, b"-MF") || eq(f, b"-MT") || eq(f, b"-MQ") || eq(f, b"-Xclang") || eq(
        f,
        b"-Xpreprocessor",
    ) || eq(f, b"-target") || eq(f, b"-isysroot") || eq(f, b"-cxx-isystem") || eq(f, b"-isystem-after") || takes_value_more_exec(f)
}

fn takes_value_more_exec(f: &Vec<u8>) -> (r: bool)
    ensures
        r == takes_value_more(f@),
{
    eq(f, b"-F") || eq(f, b"-L") || eq(f, b"-l") || eq(f, b"-B") || eq(f, b"-z") || eq(f, b"-u") || eq(f, b"-e") || eq(f, b"-T") || eq(f, b"-rpath") || eq(f, b"-arch") || eq(f, b"-dumpdir") || eq(f, b"-Xlinker") || eq(f, b"-Xassembler") || eq(f, b"-Xanalyzer") || eq(f, b"-Xarch_host") || eq(f, b"-Xarch_device") || eq(f, b"-mllvm") || eq(f, b"-iprefix") || eq(f, b"-iwithprefix") || eq(f, b"-iwithprefixbefore") || eq(f, b"-iframework") || eq(f, b"-iwithsysroot") || eq(f, b"-ivfsoverlay") || eq(f, b"-stdlib++-isystem") || eq(f, b"--sysroot") || eq(f, b"-working-directory") || eq(f, b"-module-dependency-dir") || eq(f, b"-resource-dir") || eq(f, b"-fdebug-compilation-dir") || eq(f, b"-serialize-diagnostics") || eq(f, b"--serialize-diagnostics") || eq(f, b"--param") || eq(f, b"--language") || eq(f, b"--output") || eq(f, b"--include-directory") || eq(f, b"--define-macro") || eq(f, b"--undefine-macro") || eq(f, b"--include") || eq(f, b"--imacros") || eq(f, b"--prefix") || eq(f, b"--system-header-prefix") || eq(f, b"--library-directory")
}

fn fault_exec(fl: &Vec<Vec<u8>>, cs: &Vec<Vec<u8>>, i: usize, last: Option<usize>) -> (r: Option<FlagFault>)
    requires
        i < fl.len(),
        match last {
            Some(j) => last_contract(fl@, fl.len() as int) == Some(j as int),
            None => last_contract(fl@, fl.len() as int) is None,
        },
    ensures
        r == fault(fl@, cs@, i as int),
{
    let f = &fl[i];
    let c = contraction_exec(f);
    let contracts = last == Some(i) && c != 1;
    let denormals = starts_exec(f, b"-fdenormal-fp-math=") && !eq(f, b"-fdenormal-fp-math=ieee");
    let eval = starts_exec(f, b"-ffp-eval-method=") && !eq(f, b"-ffp-eval-method=source");
    if contracts || denormals || eval || float_exec(f) || x87_exec(fl, i) {
        return Some(FlagFault::Float);
    }
    if eq(f, b"--std") || eq(f, b"-ansi") || eq(f, b"--ansi") {
        return Some(FlagFault::Std);
    }
    if let Some(ok) = std_exec(f) {
        if !ok {
            return Some(FlagFault::Std);
        }
    }
    if reads_exec(f) {
        Some(FlagFault::Reads)
    } else if starts_exec(f, b"@") {
        Some(FlagFault::ResponseFile)
    } else if eq(f, b"--config") || starts_exec(f, b"--config=") {
        Some(FlagFault::ConfigFile)
    } else if eq(f, b"-w") || eq(f, b"-Wno-everything") || eq(f, b"--no-warnings") {
        Some(FlagFault::HidesAll)
    } else if starts_exec(f, b"-Wno-") && names_warning_exec(cs, f) {
        Some(FlagFault::HidesRow)
    } else if takes_value_exec(f) && (i + 1 == fl.len() || (fl[i + 1].len() > 1 && fl[i + 1][0] == 0x2d)) {
        Some(FlagFault::Swallows)
    } else {
        None
    }
}

/// The check of the flags of the compiler, decision 0128.
pub fn check_flags(fl: &Vec<Vec<u8>>, cs: &Vec<Vec<u8>>) -> (r: FlagCheck)
    ensures
        r.faults@ == faults(fl@, cs@, fl.len() as int),
        r.no_std == !(exists|i: int| 0 <= i < fl.len() && #[trigger] std_value(fl@[i]@) is Some),
        r.no_contract_off == !(exists|i: int| 0 <= i < fl.len() && #[trigger] is_off(fl@[i]@)),
        r.faults@.len() == 0 && !r.no_std && !r.no_contract_off ==> clean(fl@, cs@),
{
    // The last flag that sets contraction.
    let mut last: Option<usize> = None;
    let mut k = 0;
    while k < fl.len()
        invariant
            k <= fl.len(),
            match last {
                Some(j) => last_contract(fl@, k as int) == Some(j as int),
                None => last_contract(fl@, k as int) is None,
            },
        decreases fl.len() - k,
    {
        if contraction_exec(&fl[k]) != 0 {
            last = Some(k);
        }
        k += 1;
    }
    let mut out: Vec<(usize, FlagFault)> = Vec::new();
    let mut has_std = false;
    let mut has_off = false;
    let mut i = 0;
    while i < fl.len()
        invariant
            i <= fl.len(),
            match last {
                Some(j) => last_contract(fl@, fl.len() as int) == Some(j as int),
                None => last_contract(fl@, fl.len() as int) is None,
            },
            out@ == faults(fl@, cs@, i as int),
            has_std == (exists|j: int| 0 <= j < i && #[trigger] std_value(fl@[j]@) is Some),
            has_off == (exists|j: int| 0 <= j < i && #[trigger] is_off(fl@[j]@)),
        decreases fl.len() - i,
    {
        match fault_exec(fl, cs, i, last) {
            Some(k) => out.push((i, k)),
            None => {},
        }
        if std_exec(&fl[i]).is_some() {
            has_std = true;
        }
        if contraction_exec(&fl[i]) == 1 {
            has_off = true;
        }
        i += 1;
    }
    proof {
        lemma_faults_empty(fl@, cs@, fl.len() as int);
        lemma_last_contract(fl@, fl.len() as int);
        if out@.len() == 0 && has_std && has_off {
            let n = fl.len() as int;
            assert forall|j: int| 0 <= j < n && #[trigger] std_value(fl@[j]@) is Some implies std_ok(std_value(fl@[j]@).unwrap()) by {
                assert(fault(fl@, cs@, j) is None);
            }
            let w = choose|j: int| 0 <= j < n && #[trigger] is_off(fl@[j]@);
            assert(contraction(fl@[w]@) is Some);
            let j = last_contract(fl@, n).unwrap();
            assert(fault(fl@, cs@, j) is None);
            assert forall|j: int| 0 <= j < n implies flag_clean(#[trigger] fl@[j]@, cs@) by {
                assert(fault(fl@, cs@, j) is None);
            }
            assert forall|j: int| 0 <= j < n implies !#[trigger] swallows(fl@, j) by {
                assert(fault(fl@, cs@, j) is None);
            }
            assert forall|j: int| 0 <= j < n implies !#[trigger] x87_at(fl@, j) by {
                assert(fault(fl@, cs@, j) is None);
            }
        }
    }
    FlagCheck { faults: out, no_std: !has_std, no_contract_off: !has_off }
}

} // verus!
