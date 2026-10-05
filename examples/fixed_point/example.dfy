// A Fixed is a datatype of one int64. The product and the division by 1000 follow the C++: the product is taken in int64, and the
// division truncates toward zero, so the model divides with trunc_div, never with Dafny `/`. The contracts of add and multiply carry
// the overflow checks as preconditions on the exact integers. The conversion to a double is a real after one rounding, from
// Double.dfy. The raw value converts exactly up to 2^53, RoundExactInt says so, and the division is the one rounding, fdiv.
include "../../divergence/dafny/Double.dfy"
import opened Double
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

datatype Fixed = Fixed(raw: int64)

function iabs(x: int): int {
  if x < 0 then -x else x
}

function trunc_div(a: int, b: int): int
  requires b != 0
{
  var q := iabs(a) / iabs(b);
  if (a < 0) != (b < 0) then -q else q
}

method add(a: Fixed, b: Fixed) returns (result: Fixed)
  requires -0x8000_0000_0000_0000 <= a.raw as int + b.raw as int <= 0x7FFF_FFFF_FFFF_FFFF
  ensures result.raw as int == a.raw as int + b.raw as int
{
  result := Fixed(a.raw + b.raw);
}

method multiply(a: Fixed, b: Fixed) returns (result: Fixed)
  requires -0x8000_0000_0000_0000 <= a.raw as int * b.raw as int <= 0x7FFF_FFFF_FFFF_FFFF
  ensures result.raw as int == trunc_div(a.raw as int * b.raw as int, 1000)
  ensures iabs(1000 * result.raw as int) <= iabs(a.raw as int * b.raw as int)
  ensures iabs(a.raw as int * b.raw as int - 1000 * result.raw as int) < 1000
{
  var p: int64 := a.raw * b.raw;
  result := Fixed(trunc_div(p as int, 1000) as int64);
}

method to_double(f: Fixed) returns (result: real)
  requires -9007199254740992 <= f.raw as int <= 9007199254740992
  ensures abs(result - f.raw as real / 1000.0) <= EPS * abs(f.raw as real / 1000.0) + ETA
{
  RoundExactInt(f.raw as int);
  var whole := round(f.raw as real);
  RoundError(whole / 1000.0);
  result := fdiv(whole, 1000.0);
}

method price_with_tax(price: Fixed) returns (result: Fixed)
  requires -1_000_000_000_000_000 <= price.raw as int <= 1_000_000_000_000_000
  ensures result.raw as int == price.raw as int + trunc_div(price.raw as int * 250, 1000)
{
  var tax := multiply(price, Fixed(250));
  result := add(price, tax);
}
