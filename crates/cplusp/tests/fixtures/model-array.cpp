#include <array>
#include <cstddef>
#include <cstdint>

// A const std::array is a read-only sequence of fixed length, decision 0132. The size is the length, and the length bounds an index.
//@ requires i < 4
//@ ensures result == a[i]
int32_t pick(const std::array<int32_t, 4>& a, size_t i) {
  return a[i];
}

//@ ensures result == 3
uint64_t size(const std::array<int32_t, 3> a) {
  return a.size();
}

//@ ensures result == (a[0] || a[1])
bool any(const std::array<bool, 2>& a) {
  return a[0] || a[1];
}
