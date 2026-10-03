// Model B: the same file as model A. No rule changes it.
// A lambda with by-value captures passed to a std algorithm is a pure function. The model is one function over the seq.
// The bound on |v| keeps the count in int64.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

function Count(v: seq<int32>, k: int32): int
  decreases |v|
{
  if |v| == 0 then 0 else Count(v[..|v| - 1], k) + (if v[|v| - 1] > k then 1 else 0)
}

lemma CountAtMostLength(v: seq<int32>, k: int32)
  ensures 0 <= Count(v, k) <= |v|
  decreases |v|
{
  if |v| > 0 {
    CountAtMostLength(v[..|v| - 1], k);
  }
}

method above(v: seq<int32>, k: int32) returns (result: int64)
  requires |v| < 0x8000_0000_0000_0000
  ensures result as int == Count(v, k)
{
  CountAtMostLength(v, k);
  result := Count(v, k) as int64;
}
