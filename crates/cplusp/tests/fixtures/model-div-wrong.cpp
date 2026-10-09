#include <cstdint>

// A divisor that may be zero, and a quotient that may not fit, are named at their lines, decision 0088.
int32_t quotient(int32_t a, int32_t b) {
  return a / b;
}

//@ requires b != 0
int32_t remainder(int32_t a, int32_t b) {
  return a % b;
}

//@ ensures result == -4
int32_t euclid() {
  int32_t a = -7;
  return a / 2;
}
