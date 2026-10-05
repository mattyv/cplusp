#include <cstdint>
#include "../../include/cplusp.h"

// A const_cast is trusted. The legacy library takes a non-const reference and does not write through it. The contract has no
// modifies clause, so it says the same. The body is in trusted.cpp. The caller proves from the contract.
CPLUSP_TRUSTED("const_cast for a legacy function that only reads")
//@ ensures result == x
int32_t read_through(const int32_t& x);

//@ requires -0x40000000 <= x < 0x40000000
//@ ensures result == 2 * x
int32_t doubled(int32_t x) {
  int32_t a = read_through(x);
  int32_t b = read_through(x);
  return a + b;
}
