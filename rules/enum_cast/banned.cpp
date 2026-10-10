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
  return std::bit_cast<Kind>(b);  // BANNED also: type_punning
}

// The row holds in trusted code too, because a verified caller assumes each value is an enumerator.
CPLUSP_TRUSTED("reads a byte")
//@ ensures true
Kind by_trusted(uint8_t b) {
  return static_cast<Kind>(b);  // BANNED
}

// A cast from another enum makes a value that is no enumerator too.
enum class Wide : uint8_t { A, B, C, D, E, F, G, H };

Kind by_other(Wide w) {
  return static_cast<Kind>(w);  // BANNED
}

// A read through a pointer to the enum, in trusted code.
CPLUSP_TRUSTED("reads a byte as a Kind")
//@ ensures true
Kind by_pointer(const uint8_t& b) {
  return *reinterpret_cast<const Kind*>(&b);  // BANNED also: type_punning
}

CPLUSP_TRUSTED("reads a byte as a Kind through void")
//@ ensures true
Kind by_void(const uint8_t& b) {
  return *static_cast<const Kind*>(static_cast<const void*>(&b));  // BANNED also: type_punning
}

// std::bit_cast through a pointer to it.
CPLUSP_TRUSTED("bit casts through a pointer")
//@ ensures true
Kind by_address(uint8_t b) {
  auto p = &std::bit_cast<Kind, uint8_t>;  // BANNED also: type_punning
  return p(b);
}
