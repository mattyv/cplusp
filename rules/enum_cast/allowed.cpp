#include <cstdint>

enum class Kind : uint8_t { Small, Large };
enum class Flag : uint32_t { Read = 1, Write = 2 };

// A function makes an enumerator from a number with a case for each value.
Kind from_byte(uint8_t b) {
  if (b == 0) {
    return Kind::Small;
  }
  return Kind::Large;
}

// A cast from an enum to a number makes no value of the enum.
uint8_t to_byte(Kind k) {
  return static_cast<uint8_t>(k);
}

// An enum with values written is a set of bits, and the row does not judge it.
Flag both() {
  return static_cast<Flag>(static_cast<uint32_t>(Flag::Read) | static_cast<uint32_t>(Flag::Write));
}

// A copy of an enum value is the same value.
Kind same(Kind k) {
  Kind c = k;
  return c;
}
