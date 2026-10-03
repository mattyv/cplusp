// Model A: `++x` as `x := x + 1`. A Dafny parameter cannot be assigned, so the model uses a local.
// Dafny asks for a proof that the sum fits. For 0x7FFF_FFFF there is none.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method next(x: int32) returns (result: int32)
  ensures result as int == (x as int) + 1
{
  var y := x;
  y := y + 1;
  result := y;
}
