#include <cstdint>

// A conditional whose ensures line does not hold, and a branch that may overflow, are named at their lines, decision 0098.
//@ ensures result == (x < limit ? limit : x)
int32_t cap_wrong(int32_t x, int32_t limit) {
  return x < limit ? x : limit;
}

int32_t abs_wrong(int32_t x) {
  return x < 0 ? -x : x;
}
