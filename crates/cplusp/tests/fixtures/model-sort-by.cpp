#include <algorithm>
#include <cstdint>
#include <vector>

// std::sort with a comparator lambda is StdSort with the lambda, decision 0162. Dafny proves that the comparator is a strict weak
// order at the call.
//@ requires v.size() >= 2
//@ ensures result
bool first_two_down(const std::vector<int32_t>& v) {
  std::vector<int32_t> sorted = v;
  std::sort(sorted.begin(), sorted.end(), [](int32_t a, int32_t b) { return a > b; });
  return sorted[0] >= sorted[1];
}

// A capture by copy reads its value at the call: the values below c come first.
//@ requires v.size() >= 2
//@ ensures result
bool below_first(const std::vector<int32_t>& v, int32_t centre) {
  std::vector<int32_t> sorted = v;
  int32_t c = centre;
  std::sort(sorted.begin(), sorted.end(), [c](int32_t a, int32_t b) { return a < c && !(b < c); });
  return sorted[1] >= c || sorted[0] < c;
}
