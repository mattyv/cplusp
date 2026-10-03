// The shared model of a C++ double: a real after one rounding per operation.
//
// What it assumes about the build, and the gate cannot check: the type is IEEE 754 binary64, the rounding mode
// is round to nearest even, and the compiler keeps every operation as written, so no -ffast-math, no excess
// precision, and no contraction of a * b + c into one rounding. The float_expression row keeps one operation
// per expression, which removes the exposure to contraction.
//
// What the model leaves out: NaN, infinity and subnormal values. A contract keeps them out with a finite
// precondition and a magnitude bound. Decision 0019 records the trial.
module Float {
  const EPS: real := 1.0 / 9007199254740992.0  // 2^-53, the unit round-off
  const MAX: real := 179769313486231570000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000.0

  function abs(x: real): real { if x < 0.0 then -x else x }

  // The rounding function of the hardware. Opaque: the axioms below are all the proof knows.
  function {:axiom} round(x: real): real

  // Relative error at most EPS in the normal range. Below it the result is exact or zero in this model,
  // which is stricter than the hardware. Above MAX the hardware gives infinity and this model gives nothing.
  lemma {:axiom} RoundError(x: real)
    requires abs(x) <= MAX
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
