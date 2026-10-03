#include <cstdint>

int32_t total = 0;

// A trusted function. Its contract forgot `modifies total`.
//@ requires -0x40000000 <= x < 0x40000000
//@ requires -0x40000000 <= total < 0x40000000
//@ ensures total == old(total) + x
void add(int32_t x) {
  total += x;
}

// The bot reads the contract of `add`, sees no `modifies`, and believes `total` does not change.
//@ ensures result == 0
int32_t delta() {
  int32_t before = total;
  add(1);
  return total - before;
}
