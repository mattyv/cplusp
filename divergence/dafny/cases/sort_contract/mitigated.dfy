// Model B: the same file as model A. No rule changes it.
// A std algorithm with a trusted contract is a bodyless {:axiom} method, and the model of the function calls it.
// The model of the function itself is never {:axiom}, because Dafny would then trust its contract without a proof.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

predicate Sorted(s: seq<int32>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method {:axiom} std_sort(v0: seq<int32>) returns (v: seq<int32>)
  ensures Sorted(v)
  ensures multiset(v) == multiset(v0)

method sort_in_place(v0: seq<int32>) returns (v: seq<int32>)
  ensures Sorted(v)
  ensures multiset(v) == multiset(v0)
{
  v := std_sort(v0);
}
