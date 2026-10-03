enum Color { Red, Green };  // BANNED

enum Mode : unsigned { Fast, Slow };  // BANNED

enum { Mask = 3 };  // BANNED

int code(Color c) {
  return c == Red ? Mask : Fast;
}
