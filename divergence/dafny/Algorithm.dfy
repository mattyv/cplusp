// The model of the std algorithms that the translator calls, decision 0160. The shell includes this file in a model that sorts.
module Algorithm {
  // A strict weak order, C++23 [alg.sorting.general] paragraph 4: irreflexive, transitive, and the equivalence is transitive.
  ghost predicate StrictWeakOrder<T(!new)>(cmp: (T, T) -> bool) {
    (forall a :: !cmp(a, a))
    && (forall a, b, c :: cmp(a, b) && cmp(b, c) ==> cmp(a, c))
    && (forall a, b, c :: !cmp(a, b) && !cmp(b, a) && !cmp(b, c) && !cmp(c, b) ==> !cmp(a, c) && !cmp(c, a))
  }

  // A sorted range, C++23 [alg.sorting.general] paragraph 5: no later element compares less than an earlier one.
  ghost predicate SortedBy<T>(s: seq<T>, cmp: (T, T) -> bool) {
    forall i, j :: 0 <= i < j < |s| ==> !cmp(s[j], s[i])
  }

  // The model of std::sort, decision 0160. A caller sees the contract only, because this is a method. The contract is the
  // trusted part: C++23 [sort] says that std::sort sorts the elements, and [alg.sorting.general] defines a sorted range and
  // requires a strict weak order. The body is an insertion sort, so Dafny shows that a sort can meet the contract for each
  // input that it allows. A contract that no sort can meet would let a caller prove false.
  method StdSort<T(!new)>(v0: seq<T>, cmp: (T, T) -> bool) returns (v: seq<T>)
    requires StrictWeakOrder(cmp)
    ensures SortedBy(v, cmp)
    ensures multiset(v) == multiset(v0)
    ensures |v| == |v0|
  {
    v := [];
    var n := 0;
    while n < |v0|
      invariant 0 <= n <= |v0|
      invariant SortedBy(v, cmp)
      invariant multiset(v) == multiset(v0[..n])
    {
      var x := v0[n];
      // The first place where the element is not below x.
      var i := 0;
      while i < |v| && cmp(v[i], x)
        invariant 0 <= i <= |v|
        invariant forall k :: 0 <= k < i ==> cmp(v[k], x)
      {
        i := i + 1;
      }
      var w := v[..i] + [x] + v[i..];
      assert SortedBy(w, cmp) by {
        forall p, q | 0 <= p < q < |w| ensures !cmp(w[q], w[p]) {
          if q == i {
            // The element before x is below x, so x is not below it.
            assert cmp(v[p], x);
            if cmp(x, v[p]) { assert cmp(v[p], v[p]); }
          } else if p == i {
            // An element after x is not below x: directly at i, and through v[i] after it.
            assert w[q] == v[q - 1];
            if q - 1 == i {
              assert !cmp(v[i], x);
            } else {
              assert !cmp(v[q - 1], v[i]);
              assert !cmp(v[i], x);
              if cmp(v[q - 1], x) {
                if cmp(x, v[i]) { assert cmp(v[q - 1], v[i]); }
                else { assert !cmp(v[i], x) && !cmp(x, v[i]); assert !cmp(v[q-1], v[i]) && !cmp(v[i], v[q-1]) ==> !cmp(v[q-1], x); 
                  if cmp(v[i], v[q - 1]) { assert cmp(v[i], x); } }
              }
            }
          } else {
            var p' := if p < i then p else p - 1;
            var q' := if q < i then q else q - 1;
            assert w[p] == v[p'] && w[q] == v[q'] && p' < q';
          }
        }
      }
      assert v0[..n + 1] == v0[..n] + [x];
      assert v == v[..i] + v[i..];
      assert multiset(w) == multiset(v) + multiset{x};
      v := w;
      n := n + 1;
    }
    assert v0[..|v0|] == v0;
    assert |multiset(v)| == |multiset(v0)|;
  }
}

