// Model B: the promotion is written out. In C++ false becomes 0 and true becomes 1.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method count_true(a: bool, b: bool) returns (result: int32)
  ensures result as int == (if a then 1 else 0) + (if b then 1 else 0)
{
  result := (if a then 1 else 0) + (if b then 1 else 0);
}
