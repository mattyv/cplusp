#include <cstdint>
// A call before its statement keeps the requires lines of its callee, and its value is the value of the callee, decision 0104.
//@ requires x < 1000
//@ ensures result == x + 1
int32_t inc(int32_t x) {
  return x + 1;
}

int32_t unguarded(int32_t x) {
  return inc(x) + 0;
}

//@ requires x < 500
//@ ensures result == x + 3
int32_t off(int32_t x) {
  return inc(inc(x));
}
