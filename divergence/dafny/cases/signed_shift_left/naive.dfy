// Model A: `x << n` carried over on the bounded int32. Dafny has shifts on bit-vector types only.
// The literal line is a type error.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000

method shl(x: int32, n: uint32) returns (result: int32)
  requires n < 32
{
  result := x << n;
}
