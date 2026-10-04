#include <cstdint>

// A const_cast is trusted. The legacy library takes a non-const reference and does not write through it, and the contract says
// so with an empty modifies clause. The body is in trusted.cpp. The caller proves from the contract.
//@ ensures result == x
int32_t read_through(const int32_t& x);

//@ requires -0x40000000 <= x < 0x40000000
//@ ensures result == 2 * x
int32_t doubled(int32_t x) {
  int32_t a = read_through(x);
  int32_t b = read_through(x);
  return a + b;
}
