#include <cstddef>
#include <cstdint>
#include <vector>

// Slices in a contract, decision 0085: examples/recursion, with Count in model-slice.spec.dfy.
//@ requires v.size() <= 10000
//@ requires i <= v.size()
//@ decreases v.size() - i
//@ ensures result <= v.size() - i
//@ ensures result == Count(v[i..], x)
size_t count_equal(const std::vector<int32_t>& v, size_t i, int32_t x) {
  if (i == v.size()) {
    return 0;
  }
  size_t rest = count_equal(v, i + 1, x);
  if (v[i] == x) {
    return rest + 1;
  }
  return rest;
}

//@ requires v.size() >= 3
//@ ensures v[1..3].size() == 2 && v[..2][1] == v[1] && !v[1..].empty()
bool parts(const std::vector<int32_t>& v) {
  return true;
}
