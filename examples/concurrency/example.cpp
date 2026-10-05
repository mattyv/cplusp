#include <cstdint>
#include "../../include/cplusp.h"

// A value another thread changes enters verified code through a trusted getter. Its contract says what every writer keeps, a range,
// and nothing about two reads being equal. The body is in trusted.cpp.
CPLUSP_TRUSTED("an atomic load of a level that other threads write")
//@ ensures 0 <= result <= 100
int32_t level();

// The caller reads once, and uses the range for something real: the headroom is never negative and never above 100.
//@ ensures 0 <= result <= 100
int32_t headroom() {
  return 100 - level();
}
