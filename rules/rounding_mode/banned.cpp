#include <cfenv>

double rounded_up(double a, double b) {
  std::fesetround(FE_UPWARD);  // BANNED
  return a + b;
}

void restore(const std::fenv_t& saved) {
  std::fesetenv(&saved);  // BANNED
}

#include <xmmintrin.h>

void flush_to_zero() {
  _mm_setcsr(_mm_getcsr() | 0x8040);  // BANNED also: inline_asm_intrinsics
}
