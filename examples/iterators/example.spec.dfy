// Sum is the specification of total: the sum of a sequence, with no bound.
function Sum(s: seq<int32>): int
  decreases |s|
{
  if |s| == 0 then 0 else Sum(s[..|s| - 1]) + s[|s| - 1] as int
}
