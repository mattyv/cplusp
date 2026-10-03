//@ ensures result == a
double shifted(double a, double b) {
  double s = a + b;
  return s - b;
}
