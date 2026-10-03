#include <cstdint>

//@ requires x < 0x7FFFFFFF
//@ modifies x
//@ ensures x == old(x) + 1
//@ ensures result == old(x)
int32_t next(int32_t& x) {
  return x++;
}

//@ ensures result == (a < b)
bool before(int32_t a, int32_t b) {
  return a < b;
}

//@ requires x < 0x7FFFFFFE
//@ modifies x
//@ ensures x == old(x) + 2
//@ ensures result == true
bool rises(int32_t& x) {
  return before(next(x), next(x));
}
