#include <cstddef>
#include <cstdint>
#include <vector>

// Two reads on one line that may each be out of range give two lines, decision 0164.
//@ requires i < 1000
//@ requires j < 1000
int32_t two(const std::vector<int32_t>& v, size_t i, size_t j) {
  return v[i] + v[j];
}
