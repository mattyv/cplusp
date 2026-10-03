#include <cstdint>

int32_t steps(int32_t k) {
  int32_t r = 0;
  switch (k) {
    case 1:
      r = 1;
    case 2:  // BANNED
      r += 2;
      break;
    default:
      r = -1;
  }
  return r;
}
