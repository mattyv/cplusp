// A std algorithm with a trusted contract is a bodyless {:axiom} method, and the model of the function calls it. The model of
// the function itself is a real method, so Dafny proves it. A sorted permutation has its smallest element first. The count_if
// and its lambda are one function over the seq, Negatives, with a bound on its value.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

predicate Sorted(s: seq<int32>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method {:axiom} std_sort(v0: seq<int32>) returns (v: seq<int32>)
  ensures Sorted(v)
  ensures multiset(v) == multiset(v0)

method minimum(v: seq<int32>) returns (result: int32)
  requires |v| > 0
  ensures forall j :: 0 <= j < |v| ==> result <= v[j]
  ensures exists j :: 0 <= j < |v| && v[j] == result
{
  var sorted := std_sort(v);
  assert |sorted| == |v| by {
    assert |multiset(sorted)| == |multiset(v)|;
  }
  result := sorted[0];
  assert result in multiset(sorted);
  assert result in multiset(v);
  forall j | 0 <= j < |v|
    ensures result <= v[j]
  {
    assert v[j] in multiset(v);
    assert v[j] in multiset(sorted);
    var k :| 0 <= k < |sorted| && sorted[k] == v[j];
  }
}

function Negatives(v: seq<int32>): int
  decreases |v|
{
  if |v| == 0 then 0 else Negatives(v[..|v| - 1]) + (if v[|v| - 1] < 0 then 1 else 0)
}

lemma NegativesAtMostLength(v: seq<int32>)
  ensures 0 <= Negatives(v) <= |v|
  decreases |v|
{
  if |v| > 0 {
    NegativesAtMostLength(v[..|v| - 1]);
  }
}

method count_negative(v: seq<int32>) returns (result: int32)
  requires |v| <= 0x7FFF_FFFF
  ensures result as int == Negatives(v)
{
  NegativesAtMostLength(v);
  result := Negatives(v) as int32;
}
