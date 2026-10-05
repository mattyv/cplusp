#include <cstdint>
#include "../../include/cplusp.h"

// Shared ownership is trusted, and the contract speaks of the value and not of the reference count. The body is in trusted.cpp.
// The caller uses the value, and the prover proves from the contract.
CPLUSP_TRUSTED("shared ownership, and the contract speaks of the value only")
//@ ensures result == x
int32_t shared_value(int32_t x);

//@ requires -0x40000000 <= x < 0x40000000
//@ ensures result == x + 1
int32_t next_value(int32_t x) {
  return shared_value(x) + 1;
}
