#include <cfloat>

//@ requires |a| <= DBL_MAX / 4
//@ ensures |result - a * 0.1| <= eps * |a * 0.1| + eta
double tenth(double a) {
  return a * 0.1;  // BANNED
}

constexpr double TOLERANCE = 1e-8;  // BANNED

double price() {
  return 2.675;  // BANNED
}
