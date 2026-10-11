#include <cstdint>

// A character that the eye cannot see is named by its code point, decisions 0125 and 0126.
//@ requires x <​ 1
int32_t zw(int32_t x) {
  return x;
}

//@ ensures result ‮== x
int32_t rl(int32_t x) {
  return x;
}
