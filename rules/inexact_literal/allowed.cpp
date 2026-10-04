#include <cfloat>

//@ requires |a| <= DBL_MAX / 4
//@ ensures |result - a / 10| <= eps * |a / 10| + eta
double tenth(double a) {
  return a / 10.0;
}

//@ requires |a| <= DBL_MAX / 4
//@ ensures |result - a * 0.5| <= eps * |a * 0.5| + eta
double half(double a) {
  return a * 0.5;
}

// The exact value of the double nearest to a tenth, spelled as a hex float.
constexpr double TENTH = 0x1.999999999999ap-4;

//@ requires |a| <= DBL_MAX / 4
//@ ensures |result - a * 0.1000000000000000055511151231257827021181583404541015625| <= eps * |a * 0.1000000000000000055511151231257827021181583404541015625| + eta
double tenth_by_constant(double a) {
  return a * TENTH;
}

double thousand() {
  return 1e3;
}
