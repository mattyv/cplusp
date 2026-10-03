// Model B: the wrap is written out. Dafny's `%` on int is never negative, so it is the C++ modulus.
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000

function wrap32(x: int): uint32 {
  (x % 0x1_0000_0000) as uint32
}

method sub(a: uint32, b: uint32) returns (result: uint32)
  ensures result as int == ((a as int) - (b as int)) % 0x1_0000_0000
{
  result := wrap32((a as int) - (b as int));
}
