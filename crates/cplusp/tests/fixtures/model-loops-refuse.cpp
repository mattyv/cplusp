#include <cstdint>

// Loops and writes with no rule are refused at their lines, decision 0061.
int32_t write_param(int32_t x) {
  x = 1;
  return x;
}

int32_t compound(int32_t x) {
  int32_t y = x;
  y += 1;
  return y;
}

int32_t breaks(int32_t n) {
  int32_t i = 0;
  while (i < n) {
    break;
  }
  return i;
}

int32_t unbound(int32_t n) {
  int32_t i = 0;
  //@ invariant i <= z
  while (i < n) {
    ++i;
  }
  return i;
}

//@ invariant x > 0
int32_t misplaced_on_function(int32_t x) {
  return x;
}

int32_t misplaced_on_loop(int32_t x) {
  int32_t i = 0;
  //@ ensures i > 0
  while (i < x) {
    ++i;
  }
  return i;
}

int32_t result_in_loop(int32_t n) {
  int32_t i = 0;
  //@ invariant result == 0
  while (i < n) {
    ++i;
  }
  return i;
}

int32_t forever() {
  for (;;) {
    return 1;
  }
}
