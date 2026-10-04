#include <cstdint>

// constexpr changes nothing for the prover. A constexpr function is a pure function, and a call at run time has the same
// contract as any other call. The compiler checks only the calls it evaluates at compile time.
constexpr int32_t kScale = 10;

//@ requires -0x7FFFFF <= x <= 0x7FFFFF
//@ ensures result == x * kScale
constexpr int32_t scaled(int32_t x) {
  return x * kScale;
}

//@ requires -0x7FFFFF <= a <= 0x7FFFFF
//@ requires -0x7FFFFF <= b <= 0x7FFFFF
//@ ensures result == (a + b) * kScale
int32_t scaled_sum(int32_t a, int32_t b) {
  return scaled(a) + scaled(b);
}
