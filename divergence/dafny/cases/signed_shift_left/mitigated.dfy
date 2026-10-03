// Model B: the shift goes through bv32, and two helpers convert. C++20 shifts the two's-complement bits.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000

// A negative value has the bit pattern of the value plus 2^32.
function to_bv32(x: int32): bv32 {
  if x < 0 then ((x as int) + 0x1_0000_0000) as bv32 else x as bv32
}

// A pattern with the top bit set is the value minus 2^32.
function from_bv32(b: bv32): int32 {
  if b >= 0x8000_0000 then ((b as int) - 0x1_0000_0000) as int32 else b as int32
}

lemma BackAndForth(b: bv32)
  ensures to_bv32(from_bv32(b)) == b
{
}

method shl(x: int32, n: uint32) returns (result: int32)
  requires n < 32
  ensures to_bv32(result) == to_bv32(x) << n
{
  result := from_bv32(to_bv32(x) << n);
  BackAndForth(to_bv32(x) << n);
}
