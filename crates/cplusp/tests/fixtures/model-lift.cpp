#include <cstdint>

// A call inside an expression runs before its statement, when C++ always evaluates it once, decision 0104.
//@ requires x < 1000
//@ ensures result == x + 1
int32_t inc(int32_t x) {
  return x + 1;
}

//@ requires x < 998
//@ ensures result == x + 3
int32_t three(int32_t x) {
  return inc(inc(x)) + 1;
}

//@ requires x < 500
//@ ensures result == (x + 1 > 100)
bool big(int32_t x) {
  return inc(x) > 100;
}

//@ requires -1000 < x && x < 500
//@ ensures result == 2 * x + 2
int32_t twice(int32_t x) {
  int32_t y = inc(x) + inc(x);
  if (inc(y) > 0) {
    return y;
  }
  return y;
}
