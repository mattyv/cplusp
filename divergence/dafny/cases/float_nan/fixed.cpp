#include <cfloat>
#include <cmath>

// eps is DBL_EPSILON / 2 and eta is DBL_TRUE_MIN / 2. The tolerance is a double, so it carries no rounding of its own.
constexpr double T = 0x1p-30;

//@ requires std::isfinite(a) && std::isfinite(b)
//@ requires |a| <= DBL_MAX / 2 && |b| <= DBL_MAX / 2
//@ ensures result ==> |a - b| <= T + 2 * eps * T + 2 * eta
//@ ensures |a - b| <= T - 2 * eps * T - 2 * eta ==> result
bool same(double a, double b) {
  double gap = a - b;
  return gap <= T && -gap <= T;
}
