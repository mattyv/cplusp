#include <cstdint>

// Each obligation that fails is named at its C++ line, decision 0068.
//@ requires 0 <= n
int32_t entry(int32_t n) {
  int32_t i = 0;
  //@ invariant 1 <= i
  //@ decreases n - i
  while (i < n) {
    ++i;
  }
  return i;
}

//@ requires 0 <= n
int32_t kept(int32_t n) {
  int32_t i = 0;
  //@ invariant i <= 3
  //@ decreases n - i
  while (i < n) {
    ++i;
  }
  return i;
}

//@ requires x > 0
int32_t callee(int32_t x) {
  return x;
}

int32_t caller(int32_t x) {
  return callee(x);
}
