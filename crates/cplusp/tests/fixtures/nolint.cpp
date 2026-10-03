bool first(bool a) {
  if (a) {
    goto done;  // NOLINT
  }
  a = false;
done:
  return a;
}
