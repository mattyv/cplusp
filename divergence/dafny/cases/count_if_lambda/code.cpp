#include <algorithm>
#include <cstdint>
#include <vector>

//@ ensures result == the number of i with v[i] > k
int64_t above(const std::vector<int32_t>& v, int32_t k) {
  return std::count_if(v.begin(), v.end(), [k](int32_t x) { return x > k; });
}
