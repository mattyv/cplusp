#include <cstdint>

// A literal that is too large stands for no other token, decision 0082.
//@ requires forall j 99999999999999999999 j > j
//@ ensures result == x + 1
int32_t f(int32_t x) {
  return x;
}
