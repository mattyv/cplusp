#include <cstdint>

//@ requires n < 32
//@ ensures result == x * 2^n mod 2^32, in two's complement
int32_t shl(int32_t x, uint32_t n) {
  return x << n;
}
