#include <cstdint>
#include <vector>

//@ requires v.size() > 0
//@ modifies v
//@ ensures result == sum of old(v)
int32_t sum_and_double(std::vector<int32_t>& v) {
  int32_t s = 0;
  for (const int32_t x : v) {
    s += x;
    v.push_back(x);
  }
  return s;
}
