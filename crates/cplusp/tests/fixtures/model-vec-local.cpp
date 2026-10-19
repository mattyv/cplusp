#include <cstdint>
#include <vector>

// A local vector is a copy, decision 0160. A write to the copy leaves the vector of the caller as it was, and a write to the
// vector after the copy leaves the copy as it was.
//@ requires v.size() >= 1 && v[0] < 1000
//@ ensures result == v[0] + 1
int32_t bumped_first(const std::vector<int32_t>& v) {
  std::vector<int32_t> copy = v;
  copy[0] = copy[0] + 1;
  return copy[0];
}

//@ modifies v
//@ requires v.size() >= 1
//@ ensures v.size() == old(v.size()) && v[0] == 0
//@ ensures result == old(v[0])
int32_t keep_first(std::vector<int32_t>& v) {
  std::vector<int32_t> before = v;
  v[0] = 0;
  return before[0];
}

//@ requires v.size() <= 100
//@ ensures result == v.size() + 1
uint64_t grown(const std::vector<int32_t>& v) {
  std::vector<int32_t> copy = v;
  copy.push_back(7);
  return copy.size();
}

// A copy of a copy.
//@ requires v.size() >= 1
//@ ensures result == v[0]
int32_t twice(const std::vector<int32_t>& v) {
  std::vector<int32_t> a = v;
  std::vector<int32_t> b = a;
  a[0] = 5;
  return b[0];
}
