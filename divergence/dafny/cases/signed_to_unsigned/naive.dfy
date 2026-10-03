// Model A: the C++ is `return i;`, and Dafny has no implicit conversion from int32 to uint64.
// The literal line is a type error.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method index_of(i: int32) returns (result: uint64)
  ensures result as int == i as int
{
  result := i;
}
