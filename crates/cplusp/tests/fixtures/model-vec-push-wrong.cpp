#include <cstddef>
#include <cstdint>
#include <vector>

// A write past the end after push_back, and an ensures line with the wrong length, do not prove, decision 0148.
//@ modifies v
void past(std::vector<int32_t>& v) {
  v.push_back(1);
  v[v.size()] = 2;
}

//@ modifies v
//@ ensures v.size() == old(v.size()) + 2
void once(std::vector<int32_t>& v) {
  v.push_back(1);
}
