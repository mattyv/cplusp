// Model A: `x >> n` carried over on the bounded int32. Dafny has shifts on bit-vector types only.
// The literal line is a type error. The contract is the C++ one, `floor(x / 2^n)`, in integers.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000

function pow2(n: nat): nat
  ensures pow2(n) >= 1
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

method shr(x: int32, n: uint32) returns (result: int32)
  requires n < 32
  ensures result as int == (x as int) / pow2(n as int)
{
  result := x >> n;
}
