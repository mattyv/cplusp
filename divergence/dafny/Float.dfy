// The shared model of a C++ double: a real after one rounding per operation.
//
// What it assumes about the build: the type is IEEE 754 binary64, the rounding mode is round to nearest even
// with gradual underflow, and the compiler keeps every operation as written. The gate refuses -ffast-math and
// its relatives, flush-to-zero, x87 arithmetic, and any -ffp-contract other than off, because GCC fuses
// a * b + c into one rounding across statements otherwise. The rounding_mode row refuses a call that changes
// the rounding mode at run time. The float_expression row keeps one operation per expression, so the model and
// the C++ round at the same places.
//
// What the model leaves out: NaN and infinity. A contract keeps them out with a finite precondition and an
// upper magnitude bound. Decisions 0019, 0020 and 0023 record the trial, its outcome and the error axiom.
module Float {
  const EPS: real := 1.0 / 9007199254740992.0  // 2^-53, the unit round-off
  // 2^-1075, half the smallest subnormal. The absolute error a result below the normal range can carry.
  const ETA: real := 1.0 / 404804506614621236704990693437834614099113299528284236713802716054860679135990693783920767402874248990374155728633623822779617474771586953734026799881477019843034848553132722728933815484186432682479535356945490137124014966849385397236206711298319112681620113024717539104666829230461005064372655017292012526615415482186989568.0
  // DBL_MAX, the largest double, exactly 2^1024 - 2^971.
  const MAX: real := 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0

  function abs(x: real): real { if x < 0.0 then -x else x }

  // The rounding function of the hardware. Opaque: the axioms below are all the proof knows.
  function {:axiom} round(x: real): real

  // The error of one rounding: relative error at most EPS, plus half a subnormal ulp. The second term is what
  // a result below the normal range carries, down to a product that rounds to 0. Above MAX the hardware gives
  // infinity and this model gives nothing.
  lemma {:axiom} RoundError(x: real)
    requires abs(x) <= MAX
    ensures abs(round(x) - x) <= EPS * abs(x) + ETA

  // An integer up to 2^53 in magnitude is a value of the format, so it comes back as itself.
  lemma {:axiom} RoundExactInt(n: int)
    requires -9007199254740992 <= n <= 9007199254740992
    ensures round(n as real) == n as real

  // One double operation: the exact result, then one rounding.
  function fadd(a: real, b: real): real { round(a + b) }
  function fsub(a: real, b: real): real { round(a - b) }
  function fmul(a: real, b: real): real { round(a * b) }
  function fdiv(a: real, b: real): real requires b != 0.0 { round(a / b) }
}
