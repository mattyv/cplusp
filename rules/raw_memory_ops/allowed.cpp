#include <cstdint>
#include <cstddef>
#include <cstring>

struct Pair {
  int32_t a = 0;
  int32_t b = 0;
};

void copy_pair(Pair& dst, const Pair& src) {
  dst = src;
}

void copy_chars(uint8_t* dst, const uint8_t* src, std::size_t n) {
  std::memcpy(dst, src, n);
}

void clear_bytes(std::byte* dst, std::size_t n) {
  std::memset(dst, 0, n);
}
