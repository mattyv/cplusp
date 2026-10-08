// Model B: each literal with its type. The C++ is changed to add in int64_t, and Dafny checks the step in int64.
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

method positive() returns (result: bool)
  ensures result
{
  result := (2147483647 as int64) + (1 as int64) > (0 as int64);
}
