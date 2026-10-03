// Model A: the C++ is `return x;`, and Dafny has no implicit conversion from int64 to int32.
// The literal line is a type error.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

method low(x: int64) returns (result: int32)
  ensures result as int == x as int
{
  result := x;
}
