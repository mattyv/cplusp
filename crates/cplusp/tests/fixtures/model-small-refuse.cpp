#include <cstdint>

// A variable that is not constexpr is no constant, and a left shift has no rule, decision 0106.
int32_t scale = 10;

//@ ensures result == x * scale
int32_t scaled(int32_t x) {
  return x;
}

uint32_t left(uint32_t x) {
  return x << 1;
}
