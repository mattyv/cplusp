#include <cstdint>

// A SIMD intrinsic is trusted, and hot-path code goes behind a contract. The addition wraps on overflow, so the contract keeps
// the sum in range. The body is in trusted.cpp. The caller proves from the contract.
//@ requires -0x40000000 <= a < 0x40000000
//@ requires -0x40000000 <= b < 0x40000000
//@ ensures result == a + b
int32_t add_lanes(int32_t a, int32_t b);

//@ requires -0x20000000 <= a < 0x20000000
//@ requires -0x20000000 <= b < 0x20000000
//@ requires -0x40000000 <= c < 0x40000000
//@ ensures result == a + b + c
int32_t sum3(int32_t a, int32_t b, int32_t c) {
  int32_t ab = add_lanes(a, b);
  return add_lanes(ab, c);
}
