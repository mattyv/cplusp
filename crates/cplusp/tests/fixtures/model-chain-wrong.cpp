#include <cstdint>
#include <optional>

// The chain gives y < 100 and no less, decision 0131.
//@ requires 0 <= x < y < 100
//@ ensures result < 99
int32_t upper(int32_t x, int32_t y) {
  return y;
}

// `*result` with no test of has_value, decision 0131.
//@ ensures *result == x
std::optional<int32_t> keep(int32_t x) {
  if (x < 0) {
    return std::nullopt;
  }
  return x;
}
