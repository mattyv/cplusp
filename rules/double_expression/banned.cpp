double fused(double a, double b, double c) {
  return a * b + c;  // BANNED
}

double chained(double a, double b, double c) {
  return a + b + c;  // BANNED
}

bool compared(double a, double b) {
  return a - b < 0x1p-30;  // BANNED
}

double accumulated(double x, double a, double b) {
  x += a * b;  // BANNED
  return x;
}

double negated_product(double a, double b, double c) {
  return -(a * b) + c;  // BANNED
}

double cast_product(double a, double b, double c) {
  return static_cast<double>(a * b) + c;  // BANNED
}

double chosen_product(double a, double b, double c, double d, double e) {
  return (c > 0.0 ? a * b : d) + e;  // BANNED
}
