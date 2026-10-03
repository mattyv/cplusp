#include <cstddef>
#include <cstdint>
#include <vector>

int32_t low_half(int64_t x) {
  return x;  // BANNED
}

int8_t small(int32_t x) {
  int8_t s = x;  // BANNED
  return s;
}

int32_t count(const std::vector<int32_t>& v) {
  return v.size();  // BANNED
}

int32_t whole(float f) {
  return f;  // BANNED
}

uint8_t add8(uint8_t a, uint8_t b) {
  return a + b;  // BANNED
}

uint8_t bump(uint8_t a) {
  a += 100;  // BANNED
  return a;
}
