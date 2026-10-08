#include <cstdint>

// The contract is wrong: below the range the result is lo, not hi. Dafny must say so.
//@ requires lo <= hi
//@ ensures x < lo ==> result == hi
int32_t clamp(int32_t x, int32_t lo, int32_t hi) {
  if (x < lo) {
    return lo;
  }
  if (x > hi) {
    return hi;
  }
  return x;
}
