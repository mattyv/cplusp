#include <cstdint>
#include <numeric>
#include <vector>

//@ requires v.size() < 0x80000000
//@ requires every element of v is in the int32_t range
//@ ensures result == sum of v
int64_t total(const std::vector<int64_t>& v) {
  return std::accumulate(v.begin(), v.end(), int64_t{0});
}
