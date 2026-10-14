// Count is the specification of count_above: the number of elements above k. It says the same test as the lambda, with CountIf
// of the prelude, decision 0149.
function Count(s: seq<int32>, k: int): int
{
  CountIf(s, (x: int32) => x as int > k)
}
