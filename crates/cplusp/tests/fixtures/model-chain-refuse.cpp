#include <cstdint>

// A chain with two directions is refused, wherever the turn is, decision 0131.
//@ requires 0 < x < y > 5
int32_t mixed(int32_t x, int32_t y) {
  return x;
}

// `*` reads only an optional, decision 0131.
//@ requires *x > 0
int32_t star(int32_t x) {
  return x;
}
