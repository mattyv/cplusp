#include <cstdint>
#include <immintrin.h>

void pause_cpu() {
  asm("nop");  // BANNED
}

int32_t add_lanes(int32_t a, int32_t b) {
  const __m128i sum = _mm_add_epi32(_mm_set1_epi32(a), _mm_set1_epi32(b));  // BANNED
  return _mm_cvtsi128_si32(sum);  // BANNED
}
