#include <cstdint>

// A hex literal that does not fit uint64_t is refused, decision 0082. A shift in a contract has no rule.
//@ requires x < 0x1'0000'0000'0000'0000
int32_t big(int32_t x) {
  return x;
}

//@ ensures result == x << 1
int32_t shift(int32_t x) {
  return x;
}

// An octal literal means another number in C++ than its digits say, so it is refused, from the review of 0082.
//@ requires x < 010
int32_t octal(int32_t x) {
  return x;
}

//@ requires x < 1e3
int32_t exponent(int32_t x) {
  return x;
}

//@ requires x < 0x
int32_t bare(int32_t x) {
  return x;
}
