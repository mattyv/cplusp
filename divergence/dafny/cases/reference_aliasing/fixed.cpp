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

// Two objects, so the two names in the call reach two values. The contract holds: 7 and 11.
int32_t demo() {
  int32_t a = 3;
  int32_t b = 4;
  add_both(a, b);
  return a * 100 + b;
}
