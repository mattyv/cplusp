#include <cstdint>

// The bot read `n` as a local, so its contract says every call returns 1.
//@ requires n < 0x7FFFFFFF
//@ ensures result == 1
int32_t counter() {
  static int32_t n = 0;
  return ++n;
}
