#include <cstdint>

// Division truncates as in C++, decision 0088.
//@ requires b != 0 && !(a == -0x80000000 && b == -1)
//@ ensures result == a / b
int32_t quotient(int32_t a, int32_t b) {
  return a / b;
}

//@ requires b != 0 && !(a == -0x80000000 && b == -1)
//@ ensures result == a % b
int32_t remainder(int32_t a, int32_t b) {
  return a % b;
}

//@ requires b != 0
//@ ensures result == a % b && result < b
uint32_t urem(uint32_t a, uint32_t b) {
  return a % b;
}

//@ ensures result == -3
int32_t toward_zero() {
  int32_t a = -7;
  return a / 2;
}

//@ ensures result == -1
int32_t sign_of_a() {
  int32_t a = -7;
  return a % 2;
}
