// Model A: `x << n` carried over on the bounded int32. Dafny has shifts on bit-vector types only.
// The literal line is a type error. The contract is the C++ one, `x * 2^n mod 2^32`, in integers.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000

function pow2(n: nat): nat
  ensures pow2(n) >= 1
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

method shl(x: int32, n: uint32) returns (result: int32)
  requires n < 32
  ensures (result as int) % 0x1_0000_0000 == ((x as int) * pow2(n as int)) % 0x1_0000_0000
{
  result := x << n;
}
