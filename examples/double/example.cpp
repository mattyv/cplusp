#include <cfloat>
#include <cmath>

// A double is a real after one rounding per operation, so a contract gives an error bound and never an equality. Every
// parameter is finite, and the magnitudes keep the operation below DBL_MAX. Here eps is DBL_EPSILON / 2 and eta is
// DBL_TRUE_MIN / 2. The comparison uses a tolerance that is a double, and its contract has slack for the rounding of the difference.
//@ requires std::isfinite(a) && std::isfinite(b)
//@ requires |a * b| <= DBL_MAX
//@ ensures |result - a * b| <= eps * |a * b| + eta
double product(double a, double b) {
  return a * b;
}

constexpr double T = 0x1p-30;

//@ requires std::isfinite(a) && std::isfinite(b)
//@ requires |a| <= DBL_MAX / 2 && |b| <= DBL_MAX / 2
//@ ensures result ==> |a - b| <= T + 2 * eps * T + 2 * eta
//@ ensures |a - b| <= T - 2 * eps * T - 2 * eta ==> result
bool near(double a, double b) {
  double gap = a - b;
  return gap <= T && -gap <= T;
}
