#include <cstdint>

// A compound assignment as a value, a write in the condition of a loop, and a call that writes in a loop condition, decision 0177.
//@ requires x < 0x7FFFFFFE
//@ modifies x
//@ ensures result == old(x) + 2
int32_t add_two(int32_t& x) {
  return x += 2;
}

//@ requires 0 <= x && x <= 10
//@ modifies x
//@ ensures x == 11
void run_up(int32_t& x) {
  //@ invariant 0 <= x && x <= 11
  while (x++ < 10) {
  }
}

//@ requires x < 0x7FFFFFFF
//@ modifies x
//@ ensures x == old(x) + 1 && result == old(x)
int32_t next(int32_t& x) {
  return x++;
}

//@ requires 0 <= x && x <= 10
//@ modifies x
//@ ensures x == 11
void run_up_calls(int32_t& x) {
  //@ invariant 0 <= x && x <= 11
  while (next(x) < 10) {
  }
}
