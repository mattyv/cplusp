// Model A: the C++ is `return a + b;`, and Dafny has no arithmetic on bool.
// The literal line is a type error.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method count_true(a: bool, b: bool) returns (result: int32)
  ensures result as int == (if a then 1 else 0) + (if b then 1 else 0)
{
  result := a + b;
}
