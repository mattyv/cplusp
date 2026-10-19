#include <algorithm>
#include <cstdint>
#include <vector>

// A comparator that is not a strict weak order fails at the call, decision 0162.
//@ requires v.size() >= 1
int32_t at_most(const std::vector<int32_t>& v) {
  std::vector<int32_t> sorted = v;
  std::sort(sorted.begin(), sorted.end(), [](int32_t a, int32_t b) { return a <= b; });
  return 0;
}

//@ requires v.size() >= 1
int32_t always(const std::vector<int32_t>& v) {
  std::vector<int32_t> sorted = v;
  std::sort(sorted.begin(), sorted.end(), [](int32_t a, int32_t b) { return a < b || b <= a; });
  return 0;
}
