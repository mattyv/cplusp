#include <cstdint>
#include "../../include/cplusp.h"

// A variable another thread changes enters verified code through a trusted getter or through a parameter, never by a direct
// read. The getter promises a range, which every writer keeps, and nothing about two reads agreeing. The caller reads once.
CPLUSP_TRUSTED("reads a variable that another thread writes")
//@ ensures 0 <= result < 1000
int32_t read_temperature();

//@ requires 0 <= t < 1000
//@ ensures result == 1000 - t
int32_t headroom_of(int32_t t) {
  return 1000 - t;
}

//@ ensures 0 < result <= 1000
int32_t headroom() {
  int32_t t = read_temperature();
  return headroom_of(t);
}
