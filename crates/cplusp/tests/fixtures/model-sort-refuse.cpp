#include <algorithm>
#include <cstdint>
#include <vector>

// A std::sort of a form with no rule yet, decisions 0161 and 0162.
bool descending(int32_t a, int32_t b) {
  return a > b;
}

//@ requires v.size() >= 1
int32_t part(const std::vector<int32_t>& v) {
  std::vector<int32_t> x = v;
  std::sort(x.begin() + 1, x.end());
  return 0;
}

int32_t compared(const std::vector<int32_t>& v) {
  std::vector<int32_t> x = v;
  std::sort(x.begin(), x.end(), descending);
  return 0;
}

int32_t two_ranges(const std::vector<int32_t>& v) {
  std::vector<int32_t> x = v;
  std::vector<int32_t> y = v;
  std::sort(x.begin(), y.end());
  return 0;
}

int32_t wider(const std::vector<int32_t>& v) {
  std::vector<int32_t> x = v;
  std::sort(x.begin(), x.end(), [](int64_t a, int64_t b) { return a < b; });
  return 0;
}

int32_t two_statements(const std::vector<int32_t>& v) {
  std::vector<int32_t> x = v;
  std::sort(x.begin(), x.end(), [](int32_t a, int32_t b) {
    bool less = a < b;
    return less;
  });
  return 0;
}
