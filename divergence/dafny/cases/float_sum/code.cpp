//@ requires |a| <= DBL_MAX / 4
//@ requires |b| <= DBL_MAX / 4
//@ requires a + b == 0.0 || DBL_MIN <= |a + b|
//@ ensures result == a + b
double sum(double a, double b) {
  return a + b;
}
