#include <cstdint>

//@ ensures result == (a ? 1 : 0) + (b ? 1 : 0)
int32_t count_true(bool a, bool b) {
  return a + b;
}
