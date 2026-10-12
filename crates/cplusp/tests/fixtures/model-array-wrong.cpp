#include <array>
#include <cstddef>
#include <cstdint>

// The length of the array bounds an index, and no more, decision 0132.
//@ requires i <= 4
int32_t pick(const std::array<int32_t, 4>& a, size_t i) {
  return a[i];
}
