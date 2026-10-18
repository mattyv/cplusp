#include <cstdint>

// A conversion with no bound, and an absolute value that the body does not give, fail at their lines, decision 0159.
//@ ensures result == n
double widen64(int64_t n) {
  return static_cast<double>(n);
}

//@ ensures result == |n|
int32_t magnitude(int32_t n) {
  return n;
}
