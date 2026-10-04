#include <cfloat>

//@ requires |a| <= DBL_MAX / 4
//@ ensures |result - a / 10| <= eps * |a / 10| + eta
double tenth(double a) {
  return a / 10.0;
}
