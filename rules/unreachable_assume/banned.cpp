int positive(int x) {
  if (x <= 0) {
    __builtin_unreachable();  // BANNED
  }
  return x;
}

int above_hundred(int x) {
  __builtin_assume(x > 100);  // BANNED
  return x - 100;
}
