#include <cmath>

//@ requires std::isfinite(a) && std::isfinite(b)
//@ ensures result == (|a - b| <= 1e-9)
bool same(double a, double b) {
  double gap = a - b;
  return gap <= 1e-9 && -gap <= 1e-9;
}
