double fused(double a, double b, double c) {
  return a * b + c;  // BANNED
}

double chained(double a, double b, double c) {
  return a + b + c;  // BANNED
}

bool compared(double a, double b) {
  return a - b < 1e-9;  // BANNED
}

double accumulated(double x, double a, double b) {
  x += a * b;  // BANNED
  return x;
}
