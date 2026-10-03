#include <cstdint>

//@ requires n >= 0
//@ decreases n
//@ ensures result == n
int32_t depth(int32_t n) {
  if (n == 0) {
    return 0;
  }
  return 1 + depth(n - 1);
}
