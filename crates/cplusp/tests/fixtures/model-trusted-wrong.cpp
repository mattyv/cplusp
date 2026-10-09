#include <cstdint>
#include "../../../../include/cplusp.h"

// A caller that needs more than the contract of a trusted function, or that misses its requires line, fails, decision 0102.
CPLUSP_TRUSTED("reads a hardware status register")
//@ ensures result <= 255
uint32_t read_status();

//@ ensures result <= 100
uint32_t low() {
  uint32_t s = read_status();
  return s;
}

CPLUSP_TRUSTED("adds one")
//@ requires x < 1000
//@ ensures result == x + 1
int32_t increment(int32_t x);

int32_t unchecked(int32_t x) {
  int32_t y = increment(x);
  return y;
}

int32_t shifted(int32_t x) {
  return x << 1;
}
