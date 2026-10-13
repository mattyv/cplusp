#include <cstdint>
#include <vector>

// An iterator appears only as a range-for loop, and the loop body does not change the range. The prover sees a loop over the
// indexes of the range in order, decision 0143. The index line names the count of the elements before the current one, so
// an invariant can say what the running total is so far. The bounds in the contract keep the running total inside int32_t. Sum is
// the specification function, and example.spec.dfy defines it as the sum of a sequence.
//@ requires v.size() <= 1000
//@ requires forall j :: 0 <= j < v.size() ==> -1000 <= v[j] <= 1000
//@ ensures result == Sum(v)
int32_t total(const std::vector<int32_t>& v) {
  int32_t t = 0;
  //@ index i
  //@ invariant t == Sum(v[..i])
  //@ invariant -1000 * i <= t && t <= 1000 * i
  for (const int32_t x : v) {
    //@ assert v[..i + 1][..i] == v[..i]
    t += x;
  }
  //@ assert v[..v.size()] == v
  return t;
}
