#include <cstdint>

//@ requires -0x80000000 <= x < 0x80000000
//@ ensures result == x
int32_t low(int64_t x) {
  return static_cast<int32_t>(x);
}
