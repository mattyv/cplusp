#include <cstdint>
int32_t positive(int32_t x) {
  if (x <= 0) {
    __builtin_unreachable();  // BANNED
  }
  return x;
}

int32_t above_hundred(int32_t x) {
  __builtin_assume(x > 100);  // BANNED
  return x - 100;
}
