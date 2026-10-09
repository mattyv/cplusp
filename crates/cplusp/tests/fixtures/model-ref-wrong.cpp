#include <cstdint>
// A contract of a reference parameter that the body does not meet, and a call that does not meet a requires line, are named at
// their lines, decision 0108.
//@ modifies x
//@ ensures x == old(x)
void clear(int32_t& x) {
  x = 0;
}

//@ requires x < 1000
//@ modifies x
//@ ensures x == old(x) + 1
void bump(int32_t& x) {
  x += 1;
}

//@ modifies x
void bump_any(int32_t& x) {
  bump(x);
}

//@ ensures result == 1
int32_t stale() {
  int32_t a = 1;
  bump(a);
  return a;
}
