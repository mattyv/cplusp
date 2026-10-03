#include <cstdint>

//@ requires n < 64
uint64_t bit(uint32_t n) {
  return uint64_t{1} << n;
}

//@ requires n < 32
uint32_t flag(uint32_t n) {
  return 1u << n;
}

//@ requires n < 32
uint32_t shifted(uint32_t x, uint32_t n) {
  return x << n;
}
