#include <cstdint>

// Verified code computes the value. A trusted function prints it, see examples/iostreams.
//@ requires 0 < whole && 0 <= part && part <= whole
//@ ensures 0 <= result && result <= 100
int32_t percent(int32_t part, int32_t whole) {
  return static_cast<int32_t>((static_cast<int64_t>(part) * 100) / whole);
}
