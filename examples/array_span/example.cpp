#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

// A span is a pointer and a length, so it is a parameter only and never stored. The contract bounds the index. A std::array
// has a fixed size, and the size is the bound.
//@ requires s.size() > 0
//@ ensures result == s[0]
int32_t first(std::span<const int32_t> s) {
  return s[0];
}

//@ requires i < 4
//@ ensures result == a[i]
int32_t pick(const std::array<int32_t, 4>& a, size_t i) {
  return a[i];
}
