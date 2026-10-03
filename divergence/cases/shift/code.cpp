#include <cstdint>

//@ ensures result == (x * 2^n) mod 2^32
uint32_t shl(uint32_t x, uint32_t n) {
  return x << n;
}
