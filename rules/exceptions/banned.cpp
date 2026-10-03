#include <cstdint>
int32_t parse(int32_t x) {
  if (x < 0) {
    throw x;  // BANNED
  }
  return x;
}

int32_t parse_or_zero(int32_t x) {
  try {  // BANNED
    return parse(x);
  } catch (int32_t) {
    return 0;
  }
}
