#include <cstdint>

struct Sample {
  int8_t delta;
  uint16_t count;
};

// The cast to uint16_t of a sum that may not fit does not prove, decision 0138.
Sample make(int32_t a) {
  return Sample{0, static_cast<uint16_t>(a)};
}
