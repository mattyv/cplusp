#include <cfloat>
#include <cmath>

// A product with no bound, an equality that the rounding breaks, and a divisor that may be zero do not prove, decision 0154.
//@ requires std::isfinite(a) && std::isfinite(b)
//@ ensures |result - a * b| <= eps * |a * b| + eta
double unbounded(double a, double b) {
  return a * b;
}

//@ requires std::isfinite(a) && std::isfinite(b)
//@ requires |a * b| <= DBL_MAX
//@ ensures result == a * b
double exact(double a, double b) {
  return a * b;
}

//@ requires std::isfinite(a) && std::isfinite(b) && |a| <= 1.0 && |b| <= 1.0
//@ requires b != 0.0 ==> |a / b| <= DBL_MAX
double divide(double a, double b) {
  return a / b;
}
