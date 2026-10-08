#include <cstdint>

// The model never wraps, decision 0061. An unsigned value that goes below zero, and a sum of literals that overflows, each fail in
// Dafny. C++ wraps the first and has undefined behaviour for the second.
uint32_t below(uint32_t z) {
  return z - 1;
}

//@ ensures result
bool over() {
  return 2147483647 + 1 > 0;
}
