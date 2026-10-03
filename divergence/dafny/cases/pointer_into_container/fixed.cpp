#include <cstdint>
#include <vector>

//@ requires p != nullptr
//@ modifies v
//@ ensures result == old(*p)
int32_t read_after_grow(std::vector<int32_t>& v, const int32_t* p) {
  v.push_back(1);
  return *p;
}

//@ requires v.size() > 0
//@ modifies v
//@ ensures result == old(v[0])
int32_t first_then_grow(std::vector<int32_t>& v) {
  int32_t first = v[0];
  return read_after_grow(v, &first);
}
