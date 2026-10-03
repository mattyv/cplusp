#include <cstdint>
#include <vector>

//@ requires v.size() > 0
//@ modifies v
//@ ensures result == old(v[0])
int32_t first_after_grow(std::vector<int32_t>& v) {
  int32_t first = v[0];
  v.push_back(1);
  return first;
}
