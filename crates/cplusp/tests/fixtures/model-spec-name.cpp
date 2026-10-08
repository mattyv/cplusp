#include <cstdint>

// A call to a name that the companion file does not declare, decision 0079.
//@ ensures result == Min(a, b)
int32_t smaller(int32_t a, int32_t b) {
  if (a < b) {
    return a;
  }
  return b;
}
