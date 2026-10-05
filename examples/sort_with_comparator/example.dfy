// std::sort with this comparator is a bodyless {:axiom} method, and its postcondition is exactly the C++ contract: sorted by key, and
// the same multiset. The model of sorted_by_key is a real method that calls it, so Dafny proves it. The axiom says nothing about the
// order of equal keys, since std::sort promises none. smallest_key proves from the postcondition alone, as `minimum` does in algorithms.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Item = Item(key: int32, value: int32)

method {:axiom} std_sort_by(v0: seq<Item>) returns (v: seq<Item>)
  ensures forall i, j :: 0 <= i < j < |v| ==> v[i].key <= v[j].key
  ensures multiset(v) == multiset(v0)

method sorted_by_key(items: seq<Item>) returns (result: seq<Item>)
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i].key <= result[j].key
  ensures multiset(result) == multiset(items)
{
  result := std_sort_by(items);
}

method smallest_key(items: seq<Item>) returns (result: int32)
  requires |items| > 0
  ensures forall j :: 0 <= j < |items| ==> result <= items[j].key
  ensures exists j :: 0 <= j < |items| && items[j].key == result
{
  var sorted := sorted_by_key(items);
  assert |sorted| == |items| by {
    assert |multiset(sorted)| == |multiset(items)|;
  }
  result := sorted[0].key;
  assert sorted[0] in multiset(sorted);
  assert sorted[0] in multiset(items);
  forall j | 0 <= j < |items|
    ensures result <= items[j].key
  {
    assert items[j] in multiset(items);
    assert items[j] in multiset(sorted);
    var k :| 0 <= k < |sorted| && sorted[k] == items[j];
  }
}
