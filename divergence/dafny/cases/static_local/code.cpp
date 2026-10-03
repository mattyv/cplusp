#include <cstdint>

// The bot read `n` as a local, so its contract says every call returns 1.
//@ ensures result == 1
int32_t counter() {
  static int32_t n = 0;
  return ++n;
}
