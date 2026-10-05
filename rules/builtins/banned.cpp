#include <cstdint>

int32_t likely_positive(int32_t x) {
  return __builtin_expect(x > 0, 1) ? x : 0;  // BANNED
}

int32_t ones(uint32_t x) {
  return __builtin_popcount(x);  // BANNED
}

void stop() {
  __builtin_trap();  // BANNED
}
