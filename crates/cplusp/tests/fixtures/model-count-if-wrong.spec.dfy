// Count and Negatives say the same tests as the lambdas, with CountIf of the prelude, decision 0149.
function Count(s: seq<int32>, k: int): int
{
  CountIf(s, (x: int32) => x as int > k)
}

function Negatives(s: seq<int32>): int
{
  CountIf(s, (x: int32) => x < 0)
}
