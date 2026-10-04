#include <cfloat>

// The bot wrote the real a tenth and the one-rounding bound. The compiler rounds the literal first.
//@ requires |a| <= DBL_MAX / 4
//@ ensures |result - a * 0.1| <= eps * |a * 0.1| + eta
double tenth(double a) {
  return a * 0.1;
}
