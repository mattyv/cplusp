#include <cstdint>

//@ requires -1073741824 <= x < 1073741824
//@ ensures result == 2 * x
int32_t twice(int32_t x) {
  return 2 * x;
}
