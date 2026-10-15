#include <cmath>
#include "../../../../include/cplusp.h"

// A double operation that rounds, a double parameter with no isfinite, and a trusted double result with no isfinite are
// refused, decision 0150.
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
  y += 0.5;
  return y;
}
