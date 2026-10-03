#include <cstdint>
#include <span>
#include <vector>

//@ requires v.size() > 0
//@ modifies v
//@ ensures result == old(v[0])
int32_t first_after_grow(std::vector<int32_t>& v) {
  std::span<int32_t> s = v;
  v.push_back(1);
  return s[0];
}
