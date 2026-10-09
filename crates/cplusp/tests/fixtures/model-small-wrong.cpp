#include <cstdint>
// A narrowing that may not fit, and a shift that may be too wide, are named at their lines, decision 0106.
int8_t narrow(int32_t x) {
  return static_cast<int8_t>(x);
}

uint32_t shift_any(uint32_t x, uint32_t n) {
  return x >> n;
}
