// Model A: each reference parameter is an in value and an out value, separate from the other.
// That cannot say that a and b are the same object.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method add_both(a0: int32, b0: int32) returns (a: int32, b: int32)
  requires -0x1000_0000 <= a0 < 0x1000_0000
  requires -0x1000_0000 <= b0 < 0x1000_0000
  ensures a as int == (a0 as int) + (b0 as int)
  ensures b as int == (a0 as int) + 2 * (b0 as int)
{
  a := a0 + b0;
  b := b0 + a;
}

// The model proves 6 and 9 for the call add_both(x, x) with x == 3. In C++ there is one x, and it ends as 12.
method Demo() {
  var x: int32 := 3;
  var a, b := add_both(x, x);
  assert a == 6 && b == 9;
}
