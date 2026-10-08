#include <cstdint>

// A measure that does not get smaller at the recursive call, decision 0072.
//@ decreases 5
uint64_t down(uint64_t n) {
  if (n == 0) {
    return 0;
  }
  uint64_t r = down(n - 1);
  return r;
}

// A decreases line above a function names no result.
//@ decreases result
uint64_t named(uint64_t n) {
  return n;
}
