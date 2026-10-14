#include <algorithm>
#include <cstdint>
#include <vector>

// count_if with a lambda written in the call is CountIf of the prelude, decision 0149.
//@ requires v.size() <= 0x7FFFFFFF
//@ ensures result == Count(v, k)
int32_t count_above(const std::vector<int32_t>& v, int32_t k) {
  return static_cast<int32_t>(std::count_if(v.begin(), v.end(), [k](int32_t x) { return x > k; }));
}

//@ ensures result == Negatives(v)
int64_t count_negative(const std::vector<int32_t>& v) {
  return std::count_if(v.begin(), v.end(), [](const int32_t& x) { return x < 0; });
}

//@ requires v.size() < 1000
//@ modifies v
//@ ensures v.size() == old(v.size()) + 1
//@ ensures result == Count(old(v), 7) + 1
int64_t push_and_count(std::vector<int32_t>& v) {
  v.push_back(8);
  return std::count_if(v.begin(), v.end(), [](int32_t x) { return x > 7; });
}
