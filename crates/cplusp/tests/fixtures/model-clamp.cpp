#include <cstdint>

// The first slice of the translator, decision 0057: comparisons, &&, ==>, if and return.
//@ requires lo <= hi
//@ ensures lo <= result && result <= hi
//@ ensures x < lo ==> result == lo
//@ ensures x > hi ==> result == hi
//@ ensures lo <= x && x <= hi ==> result == x
int32_t clamp(int32_t x, int32_t lo, int32_t hi) {
  if (x < lo) {
    return lo;
  }
  if (x > hi) {
    return hi;
  }
  return x;
}
