#include <cstdint>

// A hex literal that does not fit uint64_t is refused, decision 0082. / and % still have no rule.
//@ requires x < 0x1'0000'0000'0000'0000
int32_t big(int32_t x) {
  return x;
}

//@ ensures result == x / 2
int32_t half(int32_t x) {
  return x;
}
