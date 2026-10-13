#include <cstddef>
#include <cstdint>
#include <vector>

// A write at an index that may be out of range, and an ensures line that the write breaks, do not prove, decision 0145.
//@ modifies v
void write_at(std::vector<int32_t>& v, size_t i, int32_t x) {
  v[i] = x;
}

//@ requires 0 < v.size()
//@ modifies v
//@ ensures v.size() == old(v.size())
//@ ensures v[0] == old(v[0])
void bump(std::vector<int32_t>& v) {
  v[0] = 7;
}
