bool first_true(bool a, bool b) {
  bool v = a;
  if (!v) {
    v = b;
  }
  return v;
}
