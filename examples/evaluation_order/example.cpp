#include <cstdint>

// One change of state in each full expression. Two calls that change state go in two statements, in the order the contract
// needs. A pair that the standard orders is allowed: the right side of && runs after the left, and only if the left is true.
//@ requires x < 0x7FFFFFFF
//@ modifies x
//@ ensures x == old(x) + 1
//@ ensures result == old(x)
int32_t next(int32_t& x) {
  return x++;
}

//@ requires 0 <= x < 0x3FFFFFFF
//@ modifies x
//@ ensures x == old(x) + 2
//@ ensures result == 2 * old(x) + 1
int32_t two_steps(int32_t& x) {
  int32_t first = next(x);
  int32_t second = next(x);
  return first + second;
}

//@ requires &x != &y
//@ requires x < 0x7FFFFFFF && y < 0x7FFFFFFF
//@ modifies x, y
//@ ensures x == old(x) + 1
//@ ensures y == (old(x) > 0 ? old(y) + 1 : old(y))
//@ ensures result == (old(x) > 0 && old(y) > 0)
bool both_positive(int32_t& x, int32_t& y) {
  return next(x) > 0 && next(y) > 0;
}
