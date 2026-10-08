#include <cstdint>

// A contract on a declaration names the parameters of that declaration. The definition may name them otherwise, decision 0060.
//@ requires -100 <= a && a <= 100
//@ requires -100 <= b && b <= 100
//@ ensures result == a - b
int32_t minus(int32_t a, int32_t b);

int32_t minus(int32_t x, int32_t y) {
  return x - y;
}
