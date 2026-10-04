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
