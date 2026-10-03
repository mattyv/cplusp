int first(int a) {
  if (a > 0) {
    goto done;  // NOLINT
  }
  a = 0;
done:
  return a;
}
