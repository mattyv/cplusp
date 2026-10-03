// Model B: the conversion is written out. In C++ every value other than 0 converts to true.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method nonzero(x: int32) returns (result: bool)
  ensures result == (x != 0)
{
  result := x != 0;
}
