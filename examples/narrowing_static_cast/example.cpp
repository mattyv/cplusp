#include <cstdint>

// A narrowing static_cast. The contract says the value fits, so the prover proves that no information is lost.
//@ requires -0x80 <= x < 0x80
//@ ensures result == x
int8_t to_byte(int32_t x) {
  return static_cast<int8_t>(x);
}
