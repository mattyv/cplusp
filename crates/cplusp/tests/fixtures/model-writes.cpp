#include <cstdint>

// A write inside an expression, decision 0177. `x++` is the old value and `++x` the new one, and the write runs first. A call
// that writes a value back runs first too, into a temporary. On the right of && and || and in a branch of ?: the write runs
// only when C++ runs it, so the statement becomes an if.
//@ requires x < 0x7FFFFFFF
//@ modifies x
//@ ensures x == old(x) + 1
//@ ensures result == old(x)
int32_t next(int32_t& x) {
  return x++;
}

//@ requires x < 0x7FFFFFFF
//@ modifies x
//@ ensures x == old(x) + 1 && result == x
int32_t bump(int32_t& x) {
  return ++x;
}

//@ requires x > -0x7FFFFFFF
//@ modifies x
//@ ensures x == old(x) - 1 && result == old(x)
int32_t back(int32_t& x) {
  int32_t old_value = x--;
  return old_value;
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

// A call that writes, inside a comparison.
//@ requires x < 0x7FFFFFFF
//@ modifies x
//@ ensures x == old(x) + 1 && result == (old(x) > 0)
bool positive_step(int32_t& x) {
  return next(x) > 0;
}

// The right side of && runs only when the left is true.
//@ requires x < 0x7FFFFFFF && y < 0x7FFFFFFF
//@ modifies x, y
//@ ensures x == old(x) + 1
//@ ensures y == (old(x) > 0 ? old(y) + 1 : old(y))
//@ ensures result == (old(x) > 0 && old(y) > 0)
bool both_positive(int32_t& x, int32_t& y) {
  return next(x) > 0 && next(y) > 0;
}

// The right side of || runs only when the left is false.
//@ requires y < 0x7FFFFFFF
//@ modifies y
//@ ensures y == (x > 0 ? old(y) : old(y) + 1)
//@ ensures result == (x > 0 || old(y) > 0)
bool either_positive(int32_t x, int32_t& y) {
  return x > 0 || next(y) > 0;
}

// A branch of ?: runs only when the condition picks it.
//@ requires x < 0x7FFFFFFF
//@ modifies x
//@ ensures x == (take ? old(x) + 1 : old(x))
//@ ensures result == (take ? old(x) : 0)
int32_t maybe_next(bool take, int32_t& x) {
  return take ? next(x) : 0;
}

//@ ensures result == (a < 10)
bool under_ten(int32_t a) {
  return a < 10;
}

// A pure call on the right of && becomes an if in the same way.
//@ ensures result == (a > 0 && a < 10)
bool small(int32_t a) {
  return a > 0 && under_ten(a);
}
