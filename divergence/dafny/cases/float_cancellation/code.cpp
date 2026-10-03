//@ requires |a| <= 1.0
//@ requires |b| <= 1.0
//@ requires 4 * eps <= |a|
//@ requires a + b == 0.0 || DBL_MIN <= |a + b|
//@ ensures result == a
double shifted(double a, double b) {
  double s = a + b;
  return s - b;
}
