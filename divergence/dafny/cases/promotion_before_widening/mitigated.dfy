// Model B: the model multiplies in the type the C++ multiplies in.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

// The C++ widens an operand, `int64_t{a} * b`. The product is in int64, and it cannot overflow.
method product(a: int32, b: int32) returns (result: int64)
  ensures result as int == (a as int) * (b as int)
{
  result := (a as int64) * (b as int64);
}

// The C++ keeps `a * b` in int32_t. Dafny asks for the fit, so the contract carries it.
method product32(a: int32, b: int32) returns (result: int32)
  requires -0x8000_0000 <= (a as int) * (b as int) < 0x8000_0000
  ensures result as int == (a as int) * (b as int)
{
  result := a * b;
}
