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

// A literal in code and one in a contract with other spellings of the same value, so a printer that moves the point fails.
//@ ensures result == 100.0
double hundred() {
  return 100.0;
}

//@ ensures result == 0.125
double eighth() {
  return 0x1p-3;
}

// A bar in the contract with no operation in code names no axiom, decision 0154.
//@ requires std::isfinite(x) && |x| <= 1.0
//@ ensures |result| <= 1.0
double unit(double x) {
  return x;
}
