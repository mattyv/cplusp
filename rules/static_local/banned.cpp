#include <cstdint>

int32_t counter() {
  static int32_t n = 0;  // BANNED
  return ++n;
}

int32_t once() {
  static const int32_t seed = 7;  // BANNED
  return seed;
}
