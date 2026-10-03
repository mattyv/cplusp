#include <cstdint>

//@ requires n < 32
//@ ensures result == floor(x / 2^n)
int32_t shr(int32_t x, uint32_t n) {
  return x >> n;
}
