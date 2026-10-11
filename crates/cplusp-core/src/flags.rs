//! The flags of the compiler that the gate refuses, decisions 0022 and 0128. The shell gives each flag after `--` as bytes, and the
//! checks of the config. The core gives the index and the reason of each refused flag, and says when a flag that the gate needs is
//! missing. It proves the facts of a run with no refusal, `check_flags`.

use vstd::prelude::*;

verus! {

/// Why the gate refuses a flag. `Float` changes floating-point results. `Std` names a standard before C++23. `Reads` changes what
/// the compiler reads or reports. `HidesAll` hides each warning, and `HidesRow` a warning that the policy names.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum FlagFault {
    Float,
    Std,
    Reads,
    ResponseFile,
    ConfigFile,
    HidesAll,
    HidesRow,
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
        == b"-fno-honor-infinities"@ || f == b"-ffp-model=fast"@ || f == b"-mfpmath=387"@ || f == b"-m32"@
}

pub open spec fn reads(f: Seq<u8>) -> bool {
    f == b"-E"@ || f == b"-P"@ || f == b"-M"@ || f == b"-MM"@ || f == b"-MV"@ || f == b"-dM"@ || f == b"-dD"@ || f == b"-dI"@ || f
        == b"-###"@ || f == b"-fdriver-only"@ || f == b"-Xpreprocessor"@ || f == b"-Xclang"@ || f == b"-include-pch"@ || starts(
        f,
        b"-Wp,"@,
    ) || starts(f, b"-fmodule"@)
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
    if contracts || denormals || eval || float_flag(f) {
        Some(FlagFault::Float)
    } else if std_value(f) is Some && !std_ok(std_value(f).unwrap()) {
        Some(FlagFault::Std)
    } else if reads(f) {
        Some(FlagFault::Reads)
    } else if starts(f, b"@"@) {
        Some(FlagFault::ResponseFile)
    } else if f == b"--config"@ || starts(f, b"--config="@) {
        Some(FlagFault::ConfigFile)
    } else if f == b"-w"@ || f == b"-Wno-everything"@ {
        Some(FlagFault::HidesAll)
    } else if starts(f, b"-Wno-"@) && names_warning(cs, rest(f, b"-Wno-"@)) {
        Some(FlagFault::HidesRow)
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
/// changes floating point, changes what the compiler reads or reports, or hides a warning of the policy.
pub open spec fn clean(fl: Seq<Vec<u8>>, cs: Seq<Vec<u8>>) -> bool {
    &&& exists|i: int| 0 <= i < fl.len() && #[trigger] std_value(fl[i]@) is Some
    &&& forall|i: int| 0 <= i < fl.len() && #[trigger] std_value(fl[i]@) is Some ==> std_ok(std_value(fl[i]@).unwrap())
    &&& last_contract(fl, fl.len() as int) matches Some(j) && is_off(fl[j]@)
    &&& forall|i: int| 0 <= i < fl.len() ==> flag_clean(#[trigger] fl[i]@, cs)
}

/// One flag that changes no floating-point result, nothing that the compiler reads or reports, and no warning of the policy, and
/// names no file of flags.
pub open spec fn flag_clean(f: Seq<u8>, cs: Seq<Vec<u8>>) -> bool {
    &&& !float_flag(f)
    &&& !(starts(f, b"-fdenormal-fp-math="@) && f != b"-fdenormal-fp-math=ieee"@)
    &&& !(starts(f, b"-ffp-eval-method="@) && f != b"-ffp-eval-method=source"@)
    &&& !reads(f)
    &&& !starts(f, b"@"@)
    &&& f != b"--config"@ && !starts(f, b"--config="@)
    &&& f != b"-w"@ && f != b"-Wno-everything"@
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
    ) || eq(f, b"-mfpmath=387") || eq(f, b"-m32")
}

fn reads_exec(f: &Vec<u8>) -> (r: bool)
    ensures
        r == reads(f@),
{
    eq(f, b"-E") || eq(f, b"-P") || eq(f, b"-M") || eq(f, b"-MM") || eq(f, b"-MV") || eq(f, b"-dM") || eq(f, b"-dD") || eq(f, b"-dI") || eq(
        f,
        b"-###",
    ) || eq(f, b"-fdriver-only") || eq(f, b"-Xpreprocessor") || eq(f, b"-Xclang") || eq(f, b"-include-pch") || starts_exec(f, b"-Wp,")
        || starts_exec(f, b"-fmodule")
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
    if contracts || denormals || eval || float_exec(f) {
        return Some(FlagFault::Float);
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
    } else if eq(f, b"-w") || eq(f, b"-Wno-everything") {
        Some(FlagFault::HidesAll)
    } else if starts_exec(f, b"-Wno-") && names_warning_exec(cs, f) {
        Some(FlagFault::HidesRow)
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
        }
    }
    FlagCheck { faults: out, no_std: !has_std, no_contract_off: !has_off }
}

} // verus!
