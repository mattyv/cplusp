// Model B: the C++ now says the value fits. Dafny keeps `as` and the caller carries the obligation.
newtype int8 = x: int | -0x80 <= x < 0x80
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method narrow(x: int32) returns (result: int8)
  requires -0x80 <= x < 0x80
  ensures result as int == x as int
{
  result := x as int8;
}
