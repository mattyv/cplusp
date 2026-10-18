#include <cmath>
#include <cstdint>

// An integer converts to a double with no rounding up to 2^53, and a contract reads an integer next to a real as that real, and
// `|e|` of an integer as its absolute value, decision 0159.
//@ ensures result == n
double widen(int32_t n) {
  return n;
}

//@ requires -9007199254740992 <= n <= 9007199254740992
//@ ensures result == n
double widen64(int64_t n) {
  return static_cast<double>(n);
}

//@ requires std::isfinite(x) && |x| <= 1000.0
//@ ensures |result - (x + k)| <= eps * |x + k| + eta
double shift(double x, int32_t k) {
  return x + k;
}

//@ requires -1000 <= n <= 1000
//@ ensures result == |n|
int32_t magnitude(int32_t n) {
  if (n < 0) {
    return -n;
  }
  return n;
}
