#include <cstdint>
#include <vector>

//@ requires &dst != &src
//@ ensures dst == old(src) && src == 0
void take(int32_t& dst, int32_t& src) {
  dst = src;
  src = 0;
}

//@ ensures result == v.size()
size_t count(const std::vector<int32_t>& v) {
  return v.size();
}

// The loop variable of a range-for is the one reference local, because it names an element for one pass.
//@ ensures v.size() == 0 ==> result == 0
int32_t last_or_zero(const std::vector<int32_t>& v) {
  int32_t r = 0;
  for (const int32_t& x : v) {
    r = x;
  }
  return r;
}
