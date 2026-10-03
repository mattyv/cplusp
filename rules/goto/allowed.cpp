int first_positive(int a, int b) {
  int v = a;
  if (v <= 0) {
    v = b;
  }
  return v;
}
