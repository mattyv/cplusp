// The shared model of a C++ double: a real after one rounding per operation.
//
// What it assumes about the build: the type is IEEE 754 binary64, the rounding mode is round to nearest even,
// and the compiler keeps every operation as written. The gate refuses -ffast-math and its relatives, and it
// requires -ffp-contract=off, because GCC fuses a * b + c into one rounding across statements otherwise. The
// float_expression row keeps one operation per expression, so the model and the C++ round at the same places.
//
// What the model leaves out: NaN, infinity and subnormal values. A contract keeps them out with a finite
// precondition and two magnitude bounds, an upper one against infinity and a lower one against subnormals.
// Decisions 0019 and 0020 record the trial and its outcome.
module Float {
  const EPS: real := 1.0 / 9007199254740992.0  // 2^-53, the unit round-off
  // 2^-1022, the smallest normal value. Below it the relative error of a product or quotient is unbounded.
  const MIN_NORMAL: real := 1.0 / 44942328371557897693232629769725618340449424473557664318357520289433168951375240783177119330601884005280028469967848339414697442203604155623211857659868531094441973356216371319075554900311523529863270738021251442209537670585615720368478277635206809290837627671146574559986811484619929076208839082406056034304.0
  const MAX: real := 179769313486231570000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000.0

  function abs(x: real): real { if x < 0.0 then -x else x }

  // The rounding function of the hardware. Opaque: the axioms below are all the proof knows.
  function {:axiom} round(x: real): real

  // Relative error at most EPS, for a result that is zero or in the normal range. A product or quotient below
  // MIN_NORMAL loses relative precision, down to a result of 0, so the contract must keep it out. Above MAX the
  // hardware gives infinity and this model gives nothing.
  lemma {:axiom} RoundError(x: real)
    requires x == 0.0 || MIN_NORMAL <= abs(x) <= MAX
    ensures abs(round(x) - x) <= EPS * abs(x)

  // An integer up to 2^53 in magnitude is a value of the format, so it comes back as itself.
  lemma {:axiom} RoundExactInt(n: int)
    requires -9007199254740992 <= n <= 9007199254740992
    ensures round(n as real) == n as real

  lemma {:axiom} RoundMonotone(x: real, y: real)
    requires x <= y
    ensures round(x) <= round(y)

  // One double operation: the exact result, then one rounding.
  function fadd(a: real, b: real): real { round(a + b) }
  function fsub(a: real, b: real): real { round(a - b) }
  function fmul(a: real, b: real): real { round(a * b) }
  function fdiv(a: real, b: real): real requires b != 0.0 { round(a / b) }
}
