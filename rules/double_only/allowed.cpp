#include <cfloat>

struct Reading {
  double value;
};

//@ requires |x| <= DBL_MAX / 2
//@ ensures |result - x * 0.5| <= eps * |x * 0.5| + eta
double half(double x) {
  const double factor = 0.5;
  return x * factor;
}

double first(const Reading& r) {
  return r.value;
}
