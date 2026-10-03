// Model A: `-x` carried over on the bounded int32. Dafny asks for a proof that the negative fits.
// For -0x8000_0000 there is none, so the model is stricter than the C++ source suggests.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method neg(x: int32) returns (result: int32)
  ensures result as int == -(x as int)
{
  result := -x;
}
