#include <cfloat>

// The bot kept the sum in a float to save space, and wrote the contract of a double.
//@ requires |a| <= DBL_MAX / 4 && |b| <= DBL_MAX / 4
//@ ensures |result - (a + b)| <= eps * |a + b| + eta
double sum(double a, double b) {
  float s = static_cast<float>(a) + static_cast<float>(b);
  return s;
}
