#include <cstddef>
#include <cstdint>
#include <vector>

//@ requires v.size() > 0
//@ modifies v
//@ ensures result == sum of old(v)
int32_t sum_and_double(std::vector<int32_t>& v) {
  int32_t s = 0;
  for (const int32_t x : v) {
    s += x;
  }
  const std::size_t n = v.size();
  for (std::size_t i = 0; i < n; ++i) {
    const int32_t y = v[i];
    v.push_back(y);
  }
  return s;
}
