//@ requires b != 0.0
//@ requires a == 0.0 || DBL_MIN <= |a / b| <= DBL_MAX
//@ ensures result == a / b
double ratio(double a, double b) {
  return a / b;
}
