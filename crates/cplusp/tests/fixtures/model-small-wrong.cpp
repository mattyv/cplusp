#include <cstdint>
// A narrowing that may not fit, and a shift that may be too wide, are named at their lines, decision 0106.
int8_t narrow(int32_t x) {
  return static_cast<int8_t>(x);
}

uint32_t shift_any(uint32_t x, uint32_t n) {
  return x >> n;
}

// The width of a 64-bit shift is 64, decision 0106.
//@ requires n <= 64
uint64_t shift_wide(uint64_t x, uint32_t n) {
  return x >> n;
}

// An unsigned constant with the top bit set has its true value in code, decision 0107.
constexpr uint8_t kByte = 200;
constexpr uint16_t kHalf = 0xFFFF;
constexpr uint32_t kMask = 0xFFFFFFFF;
constexpr uint64_t kBig = 0xFFFFFFFFFFFFFFFF;

//@ ensures result == 56
uint8_t byte_value() {
  return kByte;
}

//@ ensures result == 1
uint16_t half_value() {
  return kHalf;
}

//@ ensures result == 1
uint32_t mask_value() {
  return kMask;
}

//@ ensures result == 1
uint64_t big_value() {
  return kBig;
}

// A field hides a constant of the file with the same name, decision 0107.
constexpr int32_t kScale = 10;

struct Scaled {
  int32_t kScale;
  //@ ensures result == kScale
  int32_t get() const {
    return 10;
  }
};
