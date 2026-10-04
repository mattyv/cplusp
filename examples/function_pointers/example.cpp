#include <cstdint>

// An indirect call needs a contract on its target, so a function pointer is trusted. The trusted function calls through a
// pointer and promises what the target does. The body is in trusted.cpp. The caller proves from the contract.
//@ requires x < 0x7FFFFFFF
//@ ensures result == x + 1
int32_t increment(int32_t x);

//@ requires x < 0x7FFFFFFE
//@ ensures result == x + 2
int32_t add_two(int32_t x) {
  int32_t y = increment(x);
  return increment(y);
}
