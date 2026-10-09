#include <bit>
#include <cstdint>
#include "../../include/cplusp.h"

enum class Kind : uint8_t { Small, Large };

Kind by_static(uint8_t b) {
  return static_cast<Kind>(b);  // BANNED
}

Kind by_brace(uint8_t b) {
  return Kind{b};  // BANNED
}

Kind by_bits(uint8_t b) {
  return std::bit_cast<Kind>(b);  // BANNED
}

// The row holds in trusted code too, because a verified caller assumes each value is an enumerator.
CPLUSP_TRUSTED("reads a byte")
//@ ensures true
Kind by_trusted(uint8_t b) {
  return static_cast<Kind>(b);  // BANNED
}
