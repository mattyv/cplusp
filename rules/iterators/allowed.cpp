#include <algorithm>
#include <cstdint>
#include <vector>

int64_t total(const std::vector<int64_t>& values) {
  int64_t t = 0;
  for (const int64_t v : values) {
    t += v;
  }
  return t;
}

// begin and end may appear only as direct arguments of a std:: call.
void sort_in_place(std::vector<int64_t>& values) {
  std::sort(values.begin(), values.end());
}

int32_t sum_then_grow(std::vector<int32_t>& v) {
  int32_t s = 0;
  for (const int32_t x : v) {
    s += x;
  }
  v.push_back(s);
  return s;
}
