#include <cstdint>

// Trusted: the low three bits are a bit-field. The layout of a bit-field is implementation-defined, and the gate refuses it
// under the bitfields row, which is the point. Verified code sees only the contract in example.cpp.
// The declaration in example.cpp carries the CPLUSP_TRUSTED marker.
struct Word {
  uint32_t low : 3 = 0;
  uint32_t rest : 29 = 0;
};

uint32_t low_bits(uint32_t w) {
  Word x;
  x.low = w & 7u;
  return x.low;
}
