#include <cstdint>

int32_t total = 0;

// The contract lists the global the body changes.
//@ requires -0x40000000 <= x < 0x40000000
//@ requires -0x40000000 <= total < 0x40000000
//@ modifies total
//@ ensures total == old(total) + x
void add(int32_t x) {
  total += x;
}

// The caller changes `total` through `add`, so it lists it too, and knows the answer is 1.
//@ requires -0x40000000 <= total < 0x40000000
//@ modifies total
//@ ensures result == 1
int32_t delta() {
  int32_t before = total;
  add(1);
  return total - before;
}
