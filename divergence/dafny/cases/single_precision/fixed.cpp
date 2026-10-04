#include <cfloat>

//@ requires |a| <= DBL_MAX / 4 && |b| <= DBL_MAX / 4
//@ ensures |result - (a + b)| <= eps * |a + b| + eta
double sum(double a, double b) {
  return a + b;
}
