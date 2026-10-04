// The algorithm and the lambda are one function over the seq. Count is that function, and a bound on its value keeps the
// count inside int32. The captured k is an ordinary argument, since the capture is by value.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

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

method count_above(v: seq<int32>, k: int32) returns (result: int32)
  requires |v| <= 0x7FFF_FFFF
  ensures result as int == Count(v, k)
{
  CountAtMostLength(v, k);
  result := Count(v, k) as int32;
}
