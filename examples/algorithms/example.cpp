#include <algorithm>
#include <cstdint>
#include <vector>

// std::sort is on the trusted list, and its contract is a sorted permutation. The function sorts a copy and reads the first
// element. The caller proves that it is the smallest from the contract of sort alone.
//@ requires !v.empty()
//@ ensures forall j < v.size(): result <= v[j]
//@ ensures exists j < v.size(): v[j] == result
int32_t minimum(std::vector<int32_t> v) {
  std::sort(v.begin(), v.end());
  return v[0];
}
