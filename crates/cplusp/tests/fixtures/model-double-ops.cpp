#include <cfloat>
#include <cmath>

// Each double operation is one rounding of the model, with its error bound, decision 0154.
//@ requires std::isfinite(a) && std::isfinite(b)
//@ requires |a * b| <= DBL_MAX
//@ ensures |result - a * b| <= eps * |a * b| + eta
double product(double a, double b) {
  return a * b;
}

//@ requires std::isfinite(a) && std::isfinite(b)
//@ requires |a + b| <= DBL_MAX
//@ ensures |result - (a + b)| <= eps * |a + b| + eta
double sum(double a, double b) {
  return a + b;
}

//@ requires std::isfinite(a) && std::isfinite(b)
//@ requires b != 0.0 && |a / b| <= DBL_MAX
//@ ensures |result - a / b| <= eps * |a / b| + eta
double ratio(double a, double b) {
  return a / b;
}

//@ requires std::isfinite(a) && std::isfinite(b)
//@ requires |a - b| <= DBL_MAX
//@ ensures |result - (a - b)| <= eps * |a - b| + eta
double gap(double a, double b) {
  double d = a;
  d -= b;
  return d;
}

// A bound with no bar still rounds, and the proof names the axiom.
//@ requires std::isfinite(a) && std::isfinite(b)
//@ requires 0.0 <= a <= 1.0 && 0.0 <= b <= 1.0
//@ ensures -1.0 <= result <= 3.0
double bounded_sum(double a, double b) {
  return a + b;
}
