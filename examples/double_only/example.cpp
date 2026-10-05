#include <cmath>
#include "../../include/cplusp.h"

// Verified code has no float and no long double, because the model is of double. A float from an outside API is converted to
// double at the edge, in trusted code, and the contract is about the double. The body is in trusted.cpp.
CPLUSP_TRUSTED("a sensor library returns a float, converted to double at the edge")
//@ ensures std::isfinite(result) && -50.0 <= result <= 150.0
double sensor_reading();

// The caller clamps the reading with comparisons only, so no rounding enters its proof.
//@ ensures 0.0 <= result <= 100.0
double bounded_reading() {
  double r = sensor_reading();
  if (r < 0.0) {
    return 0.0;
  }
  if (r > 100.0) {
    return 100.0;
  }
  return r;
}
