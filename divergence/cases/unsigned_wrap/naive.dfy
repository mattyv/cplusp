// Model A: uint32_t as a bounded type. Dafny does not wrap, so the subtraction is a range error when a < b.
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000

method sub(a: uint32, b: uint32) returns (result: uint32)
  ensures result == a - b
{
  result := a - b;
}
