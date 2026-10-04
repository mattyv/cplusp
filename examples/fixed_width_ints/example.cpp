#include <cstdint>

// A sum of two 32-bit values. The contract keeps the result in range, so the proof has no overflow.
//@ requires -0x40000000 <= a < 0x40000000
//@ requires -0x40000000 <= b < 0x40000000
//@ ensures result == a + b
int32_t add(int32_t a, int32_t b) {
  return a + b;
}
