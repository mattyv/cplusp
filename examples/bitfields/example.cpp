#include <cstdint>

// The layout of a bit-field is implementation-defined, so the function that uses one is trusted, and its contract is in plain
// integers. The body is in trusted.cpp. The caller proves from the contract that the result is a number from 0 to 7.
//@ ensures result == w % 8
uint32_t low_bits(uint32_t w);

//@ ensures result == w % 8 + 1
uint32_t low_bits_plus_one(uint32_t w) {
  return low_bits(w) + 1;
}
