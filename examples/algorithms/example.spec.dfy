// Negatives is the number of elements below zero, decision 0149. SortedMin says that the first element of a sorted permutation of
// v is the smallest element of v, and that it is in v, decision 0161.
function Negatives(v: seq<int32>): nat {
  CountIf(v, (x: int32) => x < 0)
}

lemma SortedMin(s: seq<int32>, v: seq<int32>)
  requires SortedBy(s, (a: int32, b: int32) => a < b)
  requires multiset(s) == multiset(v)
  requires |v| > 0 && |s| == |v|
  ensures forall j :: 0 <= j < |v| ==> s[0] <= v[j]
  ensures exists j :: 0 <= j < |v| && v[j] == s[0]
{
  assert s[0] in multiset(v);
  forall j | 0 <= j < |v|
    ensures s[0] <= v[j]
  {
    assert v[j] in multiset(s);
    var k :| 0 <= k < |s| && s[k] == v[j];
  }
}
