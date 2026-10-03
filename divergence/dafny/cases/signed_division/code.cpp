#include <cstdint>

//@ requires b != 0
//@ requires !(a == INT32_MIN && b == -1)
//@ ensures result == a / b
int32_t quot(int32_t a, int32_t b) {
  return a / b;
}

//@ requires b != 0
//@ requires !(a == INT32_MIN && b == -1)
//@ ensures result == a % b
int32_t rem(int32_t a, int32_t b) {
  return a % b;
}
