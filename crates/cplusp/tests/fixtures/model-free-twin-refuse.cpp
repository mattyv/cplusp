#include <cstdint>

// A contract that calls a free function with two statements, and one that calls a function with a reference parameter, decision 0176.
//@ requires -1000 <= x && x <= 1000
//@ ensures result == 2 * x
int32_t twice(int32_t x) {
  int32_t y = x;
  y += x;
  return y;
}

//@ ensures result == twice(3)
int32_t six() {
  return 6;
}

//@ requires r < 1000
//@ modifies r
//@ ensures r == old(r) + 1 && result == r
int32_t bump(int32_t& r) {
  r += 1;
  return r;
}

//@ requires x < 1000
//@ ensures result == bump(x)
int32_t next(int32_t x) {
  return x + 1;
}
