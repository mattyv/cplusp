#include <cstdint>
#include <vector>

// A copy that the body writes is not the vector of the caller, decision 0160.
//@ requires v.size() >= 1
//@ ensures result == v[0]
int32_t changed(const std::vector<int32_t>& v) {
  std::vector<int32_t> copy = v;
  copy[0] = 5;
  return copy[0];
}

// A copy is not a view: it does not see a later write to the vector.
//@ modifies v
//@ requires v.size() >= 1
//@ ensures result == 0
int32_t not_a_view(std::vector<int32_t>& v) {
  std::vector<int32_t> before = v;
  v[0] = 0;
  return before[0];
}
