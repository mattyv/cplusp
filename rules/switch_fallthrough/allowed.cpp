#include <cstdint>

int32_t steps(int32_t k) {
  int32_t r = 0;
  switch (k) {
    case 1:
      r = 3;
      break;
    case 2:
      r = 2;
      break;
    default:
      r = -1;
  }
  return r;
}

int32_t meant(int32_t k) {
  int32_t r = 0;
  switch (k) {
    case 1:
      r = 1;
      [[fallthrough]];
    case 2:
      r += 2;
      break;
    default:
      r = -1;
  }
  return r;
}
