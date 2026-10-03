//@ requires |x| <= DBL_MAX / 2
//@ requires x + 1.0 == 0.0 || DBL_MIN <= |x + 1.0|
//@ ensures result == x + 1.0
double next(double x) {
  return x + 1.0;
}
