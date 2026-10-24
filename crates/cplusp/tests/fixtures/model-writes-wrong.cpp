#include <cstdint>

// A next that gives the new value, a both_positive that writes y whatever x was, and an either that writes y whatever x was,
// decision 0177.
//@ requires x < 0x7FFFFFFF
//@ modifies x
//@ ensures x == old(x) + 1
//@ ensures result == old(x)
int32_t next(int32_t& x) {
  return ++x;
}

//@ requires x < 0x7FFFFFFF
//@ modifies x
//@ ensures x == old(x) + 1 && result == old(x)
int32_t next_right(int32_t& x) {
  return x++;
}

//@ requires x < 0x7FFFFFFF && y < 0x7FFFFFFF
//@ modifies x, y
//@ ensures y == (old(x) > 0 ? old(y) + 1 : old(y))
bool both_positive(int32_t& x, int32_t& y) {
  int32_t first = next_right(x);
  int32_t second = next_right(y);
  return first > 0 && second > 0;
}

//@ requires y < 0x7FFFFFFF
//@ modifies y
//@ ensures y == old(y)
bool either_positive(int32_t x, int32_t& y) {
  return x > 0 || next_right(y) > 0;
}
