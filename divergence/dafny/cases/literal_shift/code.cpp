#include <cstdint>

//@ requires n < 63
//@ ensures result == 2^n
int64_t bit(uint32_t n) {
  return 1 << n;
}
