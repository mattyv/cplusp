// Model B: the getter is a method, and its contract says only what every writer keeps: a value from 0 to 999.
// Two calls may return two values, so `difference` cannot prove 0. It proves a bound, and `ensures result == 0` fails.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method {:axiom} read_shared() returns (result: int32)
  ensures 0 <= result < 1000

method difference() returns (result: int32)
  ensures -999 <= result <= 999
{
  var first := read_shared();
  var second := read_shared();
  result := first - second;
}
