// AddsOne says that after holds the elements of before and x, as a multiset. Inserted says that the final write of insert_sorted
// gives that: below i the elements are the old ones, above i they are the old ones one place higher, and x goes at i.
predicate AddsOne(after: seq<int32>, before: seq<int32>, x: int)
  requires -0x8000_0000 <= x < 0x8000_0000
{
  multiset(after) == multiset(before) + multiset{x as int32}
}

lemma Inserted(cur: seq<int32>, before: seq<int32>, i: int, x: int)
  requires -0x8000_0000 <= x < 0x8000_0000
  requires 0 <= i <= |before| && |cur| == |before| + 1
  requires forall k :: 0 <= k < i ==> cur[k] == before[k]
  requires forall k :: i < k < |cur| ==> cur[k] == before[k - 1]
  ensures AddsOne(cur[i := x as int32], before, x)
{
  assert cur[i := x as int32] == before[..i] + [x as int32] + before[i..];
  assert before == before[..i] + before[i..];
}
