// Count is the specification: the number of elements of s equal to x. A contract passes each integer as an exact integer.
function Count(s: seq<int32>, x: int): int
  decreases |s|
{
  if |s| == 0 then 0 else (if s[0] as int == x then 1 else 0) + Count(s[1..], x)
}
