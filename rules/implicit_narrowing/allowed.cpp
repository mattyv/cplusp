#include <cstddef>
#include <cstdint>
#include <vector>

//@ requires -0x80000000 <= x < 0x80000000
int32_t low_half(int64_t x) {
  return static_cast<int32_t>(x);
}

int64_t wide(int32_t x) {
  return x;
}

std::size_t count(const std::vector<int32_t>& v) {
  return v.size();
}

uint8_t add8(uint8_t a, uint8_t b) {
  return static_cast<uint8_t>(a + b);
}

uint8_t bump(uint8_t a) {
  a = static_cast<uint8_t>(a + 100);
  return a;
}

int8_t small() {
  int8_t s = 5;
  return s;
}

int32_t same(int32_t a) {
  a += 1;
  return a;
}

enum class Level : uint8_t { Low = 1, High = 2 };
