#include <cstdint>

// A name that is a function of the file and a function of the companion file, decision 0176.
//@ requires -1000 <= x && x <= 1000
//@ ensures result == 2 * x
int32_t twice(int32_t x) {
  return 2 * x;
}

//@ ensures result == twice(3)
int32_t six() {
  return 6;
}
