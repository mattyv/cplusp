// Model A: a method with the contract of std::sort, and no body.
// The body of std::sort is not in the model. Its contract is the trusted fact: sorted, and the same elements.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

predicate Sorted(s: seq<int32>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method {:axiom} sort_in_place(v0: seq<int32>) returns (v: seq<int32>)
  ensures Sorted(v)
  ensures multiset(v) == multiset(v0)
