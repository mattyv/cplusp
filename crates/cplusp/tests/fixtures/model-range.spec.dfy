// Sum is the sum of a sequence, the specification of total.
function Sum(s: seq<int32>): int
  decreases |s|
{
  if |s| == 0 then 0 else Sum(s[..|s| - 1]) + s[|s| - 1] as int
}
