// Model A: `1 << n` as 2^n in int64, because the result is an int64. It fits for n < 63, so Dafny proves it.
// C++ shifts the literal 1, which is an int. The wide result type does not change the width of the shift.
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000

function pow2(n: nat): nat
  ensures pow2(n) >= 1
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

lemma Pow2Monotone(a: nat, b: nat)
  requires a <= b
  ensures pow2(a) <= pow2(b)
  decreases b - a
{
  if a < b {
    Pow2Monotone(a, b - 1);
  }
}

lemma Pow2Add(a: nat, b: nat)
  ensures pow2(a + b) == pow2(a) * pow2(b)
  decreases a
{
  if a > 0 {
    Pow2Add(a - 1, b);
  }
}

lemma Pow2Of31()
  ensures pow2(31) == 0x8000_0000
{
  assert {:fuel pow2, 32, 33} pow2(31) == 0x8000_0000;
}

lemma Pow2Of62()
  ensures pow2(62) == 0x4000_0000_0000_0000
{
  Pow2Of31();
  Pow2Add(31, 31);
}

// The sizes of the powers, so that `pow2(n) as int64` is in range.
lemma Pow2Fits(n: nat)
  requires n < 63
  ensures pow2(n) < 0x8000_0000_0000_0000
{
  Pow2Monotone(n, 62);
  Pow2Of62();
}

method bit(n: uint32) returns (result: int64)
  requires n < 63
  ensures result as int == pow2(n as int)
{
  Pow2Fits(n as int);
  result := pow2(n as int) as int64;
}

// The model proves 2147483648. C++ gives -2147483648.
method Demo() {
  Pow2Of31();
  var r := bit(31);
  assert r as int == 0x8000_0000;
}
