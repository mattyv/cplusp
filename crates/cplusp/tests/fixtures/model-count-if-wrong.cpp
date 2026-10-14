#include <algorithm>
#include <cstdint>
#include <vector>

// A lambda with another test, and a count with no bound on the length, do not prove, decision 0149.
//@ requires v.size() <= 0x7FFFFFFF
//@ ensures result == Count(v, k)
int32_t at_least(const std::vector<int32_t>& v, int32_t k) {
  return static_cast<int32_t>(std::count_if(v.begin(), v.end(), [k](int32_t x) { return x >= k; }));
}

//@ ensures result == Count(v, k)
int32_t unbounded(const std::vector<int32_t>& v, int32_t k) {
  return static_cast<int32_t>(std::count_if(v.begin(), v.end(), [k](int32_t x) { return x > k; }));
}
