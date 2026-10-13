#include <cstdint>
#include <span>

// An invariant that does not hold when the loop starts, and a step that may overflow, are named at their lines, decision 0143.
//@ requires v.size() <= 1000
//@ ensures result >= 1
int32_t count_positive(std::span<const int32_t> v) {
  int32_t n = 0;
  //@ index i
  //@ invariant 1 <= n && n <= i + 1
  for (int32_t x : v) {
    if (x > 0) {
      n += 1;
    }
  }
  return n;
}

int32_t total(std::span<const int32_t> v) {
  int32_t t = 0;
  for (int32_t x : v) {
    t += x;
  }
  return t;
}
