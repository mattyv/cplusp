// Model A: `x >> n` as `x / 2^n`. Dafny `/` rounds toward negative infinity, and so does a C++20 right shift.
// The literal model is exact, so there is nothing to mitigate.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000

function pow2(n: nat): nat
  ensures pow2(n) >= 1
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

method shr(x: int32, n: uint32) returns (result: int32)
  requires n < 32
  ensures result as int == (x as int) / pow2(n as int)
{
  result := ((x as int) / pow2(n as int)) as int32;
}

// The model proves -4, and so does C++.
method Demo() {
  var r := shr(-7, 1);
  assert r == -4;
}
