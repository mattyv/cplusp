#include <cstdint>
#include "../../../../include/cplusp.h"

// A dropped write, a call too few, and a trusted callee whose requires line the caller does not meet, decision 0173.
int32_t total = 0;

//@ requires -0x40000000 <= x < 0x40000000
//@ requires -0x40000000 <= total < 0x40000000
//@ modifies total
//@ ensures total == old(total) + x
void add(int32_t x) {
  total += x;
  total -= x;
}

//@ requires -0x40000000 <= x < 0x40000000
//@ requires -0x40000000 <= total < 0x40000000
//@ modifies total
//@ ensures total == old(total) + x
void add_right(int32_t x) {
  total += x;
}

//@ requires -0x20000000 <= x < 0x20000000
//@ requires -0x20000000 <= total < 0x20000000
//@ modifies total
//@ ensures total == old(total) + 2 * x
void add_twice(int32_t x) {
  add_right(x);
}

//@ requires total < 1000
//@ modifies total
//@ ensures total == old(total) + 1
CPLUSP_TRUSTED("the count lives in a register of the device")
void tick();

//@ modifies total
//@ ensures total == old(total) + 1
void blind_tick() {
  tick();
}
