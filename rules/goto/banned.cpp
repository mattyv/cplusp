int first_positive(int a, int b) {
  int v = a;
  if (v > 0) {
    goto done;  // BANNED
  }
  v = b;
done:
  return v;
}
