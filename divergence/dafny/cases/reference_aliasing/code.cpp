#include <cstdint>

//@ requires -0x10000000 <= a < 0x10000000
//@ requires -0x10000000 <= b < 0x10000000
//@ modifies a, b
//@ ensures a == old(a) + old(b)
//@ ensures b == old(a) + 2 * old(b)
void add_both(int32_t& a, int32_t& b) {
  a += b;
  b += a;
}

// The bot passed one object twice. The contract says 6 and 9, and the object ends as 12.
int32_t demo() {
  int32_t x = 3;
  add_both(x, x);
  return x;
}
