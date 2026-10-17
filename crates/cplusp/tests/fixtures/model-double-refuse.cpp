#include <cmath>
#include "../../../../include/cplusp.h"

// A double step that rounds, a double parameter with no isfinite, a trusted double result with no isfinite and its caller are
// refused, decisions 0150 and 0154. Since 0154 the sum of line 8 is one rounding of the model.
//@ requires std::isfinite(a) && std::isfinite(b)
double sum(double a, double b) {
  return a + b;
}

double same(double x) {
  return x;
}

CPLUSP_TRUSTED("a reading from outside")
//@ ensures 0.0 <= result
double reading();

//@ requires std::isfinite(x)
double bump(double x) {
  double y = x;
  y++;
  return y;
}

double use_reading() {
  return reading();
}
