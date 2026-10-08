#include <cstdint>

// The declaration promises the first argument minus the second. The definition swaps the names, so it returns the second minus the
// first. The contract reads the declaration's names by place, decision 0060, so Dafny refuses the body.
//@ requires -100 <= x && x <= 100
//@ requires -100 <= y && y <= 100
//@ ensures result == x - y
int32_t subtract(int32_t x, int32_t y);

int32_t subtract(int32_t y, int32_t x) {
  return x - y;
}
