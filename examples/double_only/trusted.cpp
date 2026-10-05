#include <cmath>

// Trusted: a sensor library returns a float, and a float converts to a double exactly. The conversion happens once, here at the
// edge. The body keeps the contract, since a value that is no number or is out of range becomes 0.0. The gate refuses this file
// under the double_only row, which is the point. Verified code sees only the contract in example.cpp.
// The declaration in example.cpp carries the CPLUSP_TRUSTED marker.
float raw_sensor();

double sensor_reading() {
  double r = static_cast<double>(raw_sensor());
  if (!std::isfinite(r) || r < -50.0 || r > 150.0) {
    return 0.0;
  }
  return r;
}
