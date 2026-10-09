#include <cstdint>
#include "../../../../include/cplusp.h"

// A trusted function is a method with its contract and no body, and prove names it with its reason, decision 0102.
CPLUSP_TRUSTED("reads a hardware status register")
//@ ensures result <= 255
uint32_t read_status();

//@ ensures result <= 255
uint32_t headroom() {
  uint32_t s = read_status();
  return 255 - s;
}

CPLUSP_TRUSTED("a body that the translator has no rule for")
//@ requires x < 1000
//@ ensures result == x + 1
int32_t increment(int32_t x) {
  int32_t y = x;
  do {
    y = y + 1;
  } while (false);
  return y;
}

//@ requires x < 999
//@ ensures result == x + 2
int32_t add_two(int32_t x) {
  int32_t y = increment(x);
  return increment(y);
}
