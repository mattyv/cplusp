double fused(double a, double b, double c) {
  double p = a * b;
  return p + c;
}

double chained(double a, double b, double c) {
  double s = a + b;
  return s + c;
}

bool compared(double a, double b) {
  double gap = a - b;
  return gap < 1e-9;
}

double accumulated(double x, double a, double b) {
  double p = a * b;
  x += p;
  return x;
}

double negated(double a, double b) {
  return -a + b;
}
