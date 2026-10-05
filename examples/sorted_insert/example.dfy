// A vector passed by reference is an object that holds a seq. push_back appends, and each index write is a seq update.
// The invariant says what the loop has done. The elements below i are untouched. The old elements from i up sit one place higher,
// and each of them is larger than x. The decreases clause shows that the loop ends. The multiset says that nothing is lost and x is added.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

class IntVec {
  var items: seq<int32>
}

method insert_sorted(v: IntVec, x: int32)
  requires forall i, j :: 0 <= i < j < |v.items| ==> v.items[i] <= v.items[j]
  requires |v.items| < 1000000
  modifies v
  ensures |v.items| == |old(v.items)| + 1
  ensures forall i, j :: 0 <= i < j < |v.items| ==> v.items[i] <= v.items[j]
  ensures multiset(v.items) == multiset(old(v.items)) + multiset{x}
{
  ghost var s := v.items;
  v.items := v.items + [x];
  var i: uint64 := (|v.items| - 1) as uint64;
  while i > 0 && v.items[i - 1] > x
    invariant i as int <= |s|
    invariant |v.items| == |s| + 1
    invariant v.items[..i] == s[..i]
    invariant v.items[i + 1..] == s[i..]
    invariant forall j :: i as int <= j < |s| ==> s[j] > x
    decreases i
  {
    ghost var before := v.items;
    assert before[i - 1] == s[i - 1];
    v.items := v.items[i := v.items[i - 1]];
    assert v.items[..i - 1] == before[..i - 1] == s[..i - 1];
    assert v.items[i..] == [s[i - 1]] + before[i + 1..];
    assert s[i - 1..] == [s[i - 1]] + s[i..];
    i := i - 1;
  }
  v.items := v.items[i := x];
  assert v.items == s[..i] + [x] + s[i..];
  assert s == s[..i] + s[i..];
}
