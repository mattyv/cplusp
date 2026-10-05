#include <cstdint>

// Signed division and unsigned subtraction. The prover proves no overflow, no division by zero and no wrap below zero,
// so the contract says what keeps each one out. C++ division rounds toward zero, and so does the model.
//@ requires b != 0
//@ requires !(a == -0x80000000 && b == -1)
//@ ensures result == a / b
int32_t quotient(int32_t a, int32_t b) {
  return a / b;
}

//@ requires b <= a
//@ ensures result == a - b
uint32_t distance(uint32_t a, uint32_t b) {
  return a - b;
}

// A shift count stops one short of the width. Dafny shifts bit-vectors only, so the model maps this function to bv32.
//@ requires n < 32
//@ ensures result <= x
//@ ensures n == 0 ==> result == x
uint32_t shift_right(uint32_t x, uint32_t n) {
  return x >> n;
}
