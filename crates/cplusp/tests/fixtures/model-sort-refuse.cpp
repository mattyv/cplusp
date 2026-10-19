#include <algorithm>
#include <cstdint>
#include <vector>

// A std::sort of a form with no rule yet, decision 0161.
//@ requires v.size() >= 1
int32_t part(const std::vector<int32_t>& v) {
  std::vector<int32_t> x = v;
  std::sort(x.begin() + 1, x.end());
  return 0;
}

int32_t compared(const std::vector<int32_t>& v) {
  std::vector<int32_t> x = v;
  std::sort(x.begin(), x.end(), [](int32_t a, int32_t b) { return a > b; });
  return 0;
}

int32_t two_ranges(const std::vector<int32_t>& v) {
  std::vector<int32_t> x = v;
  std::vector<int32_t> y = v;
  std::sort(x.begin(), y.end());
  return 0;
}
