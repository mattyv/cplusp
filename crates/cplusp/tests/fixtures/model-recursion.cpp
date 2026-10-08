#include <cstdint>

// A recursion with its measure, decision 0072. The bound on n bounds the depth.
//@ requires n <= 1000
//@ decreases n
//@ ensures 2 * result == n * (n + 1)
uint64_t tri(uint64_t n) {
  if (n == 0) {
    return 0;
  }
  uint64_t r = tri(n - 1);
  return r + n;
}

