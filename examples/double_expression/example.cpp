#include <cfloat>
#include <cmath>

// One double operation per expression. The compiler may fuse a * b + c into one rounding. The model rounds once per
// operation, so each intermediate result has a name. The bound has one error term for each rounding, from the magnitudes.
//@ requires std::isfinite(a) && std::isfinite(b) && std::isfinite(c)
//@ requires |a * b| <= DBL_MAX / 4 && |c| <= DBL_MAX / 4
//@ ensures |result - (a * b + c)| <= 3 * eps * (|a * b| + |c|) + 3 * eta
double multiply_add(double a, double b, double c) {
  double p = a * b;
  return p + c;
}
