#include <cmath>
#include "../../../../include/cplusp.h"

// A double that only compares is a real, decision 0150.
//@ requires std::isfinite(a) && std::isfinite(b)
//@ ensures result >= a && result >= b
//@ ensures result == a || result == b
double larger(double a, double b) {
  if (a < b) {
    return b;
  }
  return a;
}

//@ requires std::isfinite(x)
//@ ensures 0.0 <= result <= 1.0
double clamp_unit(double x) {
  if (x < 0.0) {
    return 0.0;
  }
  if (x > 1.0) {
    return 1.0;
  }
  return x;
}

//@ requires std::isfinite(x)
//@ ensures result == -x
double negate(double x) {
  return -x;
}

CPLUSP_TRUSTED("a reading from outside")
//@ ensures std::isfinite(result) && 0.5 <= result <= 2.5
double scale();

//@ ensures 0.5 <= result <= 2.5
double scaled() {
  double s = scale();
  return s;
}
