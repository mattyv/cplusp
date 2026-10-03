#include <cmath>

//@ requires std::isfinite(a) && std::isfinite(b)
//@ ensures result == (a == b)
bool same(double a, double b) {
  return a <= b && b <= a;
}
