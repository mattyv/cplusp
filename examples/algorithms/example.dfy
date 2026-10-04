// A std algorithm with a trusted contract is a bodyless {:axiom} method, and the model of the function calls it. The model of
// the function itself is a real method, so Dafny proves it. A sorted permutation has its smallest element first.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

predicate Sorted(s: seq<int32>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method {:axiom} std_sort(v0: seq<int32>) returns (v: seq<int32>)
  ensures Sorted(v)
  ensures multiset(v) == multiset(v0)

method minimum(v0: seq<int32>) returns (result: int32)
  requires |v0| > 0
  ensures forall j :: 0 <= j < |v0| ==> result <= v0[j]
  ensures exists j :: 0 <= j < |v0| && v0[j] == result
{
  var v := std_sort(v0);
  assert |v| == |v0| by {
    assert |multiset(v)| == |multiset(v0)|;
  }
  result := v[0];
  assert result in multiset(v);
  assert result in multiset(v0);
  forall j | 0 <= j < |v0|
    ensures result <= v0[j]
  {
    assert v0[j] in multiset(v0);
    assert v0[j] in multiset(v);
    var k :| 0 <= k < |v| && v[k] == v0[j];
  }
}
