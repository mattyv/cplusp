// Model B: the instantiation twice<int8_t> is a method with its own types, `twice_int8`.
// In it 2 * x is computed in int, and the cast needs the result to fit. The contract of twice8 says it fits.
newtype int8 = x: int | -0x80 <= x < 0x80

method twice_int8(x: int8) returns (result: int8)
  requires -64 <= x < 64
  ensures result as int == 2 * (x as int)
{
  result := (2 * (x as int)) as int8;
}

method twice8(x: int8) returns (result: int8)
  requires -64 <= x < 64
  ensures result as int == 2 * (x as int)
{
  result := twice_int8(x);
}
