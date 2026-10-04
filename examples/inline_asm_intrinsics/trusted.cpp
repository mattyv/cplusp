#include <cstdint>
#include <immintrin.h>

// Trusted: the sum is made in a SIMD register. The gate refuses an intrinsic under the inline_asm_intrinsics row, which is the
// point. Verified code sees only the contract of add_lanes in example.cpp.
int32_t add_lanes(int32_t a, int32_t b) {
  const __m128i sum = _mm_add_epi32(_mm_set1_epi32(a), _mm_set1_epi32(b));
  return _mm_cvtsi128_si32(sum);
}
