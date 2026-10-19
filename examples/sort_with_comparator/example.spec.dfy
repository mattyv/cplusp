// SameItems says that two vectors hold the same items, as a multiset, decision 0148. SmallestKey says that the first item of a
// vector sorted by key holds the smallest key of the other vector, and that the key is in it, decision 0163.
predicate SameItems(a: seq<S_Item>, b: seq<S_Item>) {
  multiset(a) == multiset(b)
}

lemma SmallestKey(s: seq<S_Item>, v: seq<S_Item>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i].f_key <= s[j].f_key
  requires SameItems(s, v)
  requires |v| > 0
  ensures |s| == |v|
  ensures forall j :: 0 <= j < |v| ==> s[0].f_key <= v[j].f_key
  ensures exists j :: 0 <= j < |v| && v[j].f_key == s[0].f_key
{
  assert |multiset(s)| == |multiset(v)|;
  assert s[0] in multiset(v);
  forall j | 0 <= j < |v|
    ensures s[0].f_key <= v[j].f_key
  {
    assert v[j] in multiset(s);
    var k :| 0 <= k < |s| && s[k] == v[j];
  }
}
