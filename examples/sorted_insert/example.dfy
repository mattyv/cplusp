// A vector passed by reference is a seq in and a seq out, decision 0029. push_back appends, and each index write is a seq update.
// The invariant says what the loop has done. The elements below i are untouched. The elements from i up that were there before sit one place higher,
// and each of them is larger than x. The decreases clause shows that the loop ends. The multiset says that nothing is lost and x is added.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method insert_sorted(v: seq<int32>, x: int32) returns (v': seq<int32>)
  requires forall i, j :: 0 <= i < j < |v| ==> v[i] <= v[j]
  requires |v| < 1000000
  ensures |v'| == |v| + 1
  ensures forall i, j :: 0 <= i < j < |v'| ==> v'[i] <= v'[j]
  ensures multiset(v') == multiset(v) + multiset{x}
{
  var items := v + [x];
  var i: uint64 := (|items| - 1) as uint64;
  while i > 0 && items[i - 1] > x
    invariant i as int <= |v|
    invariant |items| == |v| + 1
    invariant items[..i] == v[..i]
    invariant items[i + 1..] == v[i..]
    invariant forall j :: i as int <= j < |v| ==> v[j] > x
    decreases i
  {
    ghost var before := items;
    assert before[i - 1] == v[i - 1];
    items := items[i := items[i - 1]];
    assert items[..i - 1] == before[..i - 1] == v[..i - 1];
    assert items[i..] == [v[i - 1]] + before[i + 1..];
    assert v[i - 1..] == [v[i - 1]] + v[i..];
    i := i - 1;
  }
  items := items[i := x];
  assert items == v[..i] + [x] + v[i..];
  assert v == v[..i] + v[i..];
  v' := items;
}
