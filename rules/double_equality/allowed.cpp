bool below(double a, double b) {
  return a < b;
}

//@ requires 0.0 <= tolerance
bool close(double a, double b, double tolerance) {
  double gap = a - b;
  return -tolerance <= gap && gap <= tolerance;
}
