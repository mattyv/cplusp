bool first_true(bool a, bool b) {
  bool v = a;
  if (v) {
    goto done;  // BANNED
  }
  v = b;
done:
  return v;
}
