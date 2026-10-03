int parse(int x) {
  if (x < 0) {
    throw x;  // BANNED
  }
  return x;
}

int parse_or_zero(int x) {
  try {  // BANNED
    return parse(x);
  } catch (int) {
    return 0;
  }
}
