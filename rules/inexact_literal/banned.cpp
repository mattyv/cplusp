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

// An odd integer above 2^63 is no double either: its nearest double is one away.
double huge() {
  return 9223372036854775809.0;  // BANNED
}

double huger() {
  return 18446744073709551615.0;  // BANNED
}
