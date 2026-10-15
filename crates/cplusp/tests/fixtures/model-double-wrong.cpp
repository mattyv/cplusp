#include <cmath>

// A clamp that misses part of its range does not prove, decision 0150.
//@ requires std::isfinite(x)
//@ ensures result >= 0.0
double low_clamp(double x) {
  if (x < -1.0) {
    return 0.0;
  }
  return x;
}
