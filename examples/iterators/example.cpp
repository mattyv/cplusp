#include <cstdint>
#include <vector>

// An iterator appears only as a range-for loop, and the loop body does not change the range. The prover sees a loop over the
// elements in order. The bounds in the contract keep the running total inside int32_t. Sum is the specification function,
// and example.dfy defines it as the sum of a sequence.
//@ requires v.size() <= 1000
//@ requires forall j :: 0 <= j < v.size() ==> -1000 <= v[j] <= 1000
//@ ensures result == Sum(v)
int32_t total(const std::vector<int32_t>& v) {
  int32_t t = 0;
  for (const int32_t x : v) {
    t += x;
  }
  return t;
}
