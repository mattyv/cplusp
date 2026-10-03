// Model A: uint8_t as a bounded type, and the addition done on it. The sum 255 + 1 is out of range.
newtype uint8 = x: int | 0 <= x < 0x100

method add8(a: uint8, b: uint8) returns (result: uint8)
  ensures result == a + b
{
  result := a + b;
}
