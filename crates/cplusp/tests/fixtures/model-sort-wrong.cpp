#include <algorithm>
#include <cstdint>
#include <vector>

// A sort gives no order the other way, and it may move the first element, decision 0161.
//@ requires v.size() >= 2
//@ ensures result
bool descending(const std::vector<int32_t>& v) {
  std::vector<int32_t> sorted = v;
  std::sort(sorted.begin(), sorted.end());
  return sorted[0] >= sorted[1];
}

//@ requires v.size() >= 1
//@ ensures result == v[0]
int32_t first_unchanged(const std::vector<int32_t>& v) {
  std::vector<int32_t> sorted = v;
  std::sort(sorted.begin(), sorted.end());
  return sorted[0];
}
