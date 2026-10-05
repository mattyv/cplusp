#include <cstdint>
#include "../../include/cplusp.h"

// SFINAE and template tricks have nothing to prove at run time, and their contracts are unreadable. The trusted function hides
// the template behind a plain function with a plain contract. The body is in trusted.cpp. The caller proves from the contract.
CPLUSP_TRUSTED("an enable_if template behind a plain function")
//@ requires -0x40000000 <= x < 0x40000000
//@ ensures result == 2 * x
int32_t twice32(int32_t x);

//@ requires -0x10000000 <= x < 0x10000000
//@ ensures result == 4 * x
int32_t quadruple(int32_t x) {
  int32_t t = twice32(x);
  return twice32(t);
}
