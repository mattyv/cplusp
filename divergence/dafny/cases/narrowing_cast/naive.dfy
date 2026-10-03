// Model A: the cast carried over as `as`. Dafny asks for a proof that the value fits in int8. For 200 there is none.
newtype int8 = x: int | -0x80 <= x < 0x80
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method narrow(x: int32) returns (result: int8)
  ensures result as int == x as int
{
  result := x as int8;
}
