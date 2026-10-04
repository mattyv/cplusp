// Model B: the conversion is `round`, and the contract requires an integer of at most 2^53 in magnitude.
// `RoundExactInt` then gives the exact value, so the contract is an equality and not a bound.
include "../../Double.dfy"
import opened Double

newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

method widen(n: int64) returns (result: real)
  requires -9007199254740992 <= n <= 9007199254740992
  ensures result == n as real
{
  RoundExactInt(n as int);
  result := round(n as real);
}
