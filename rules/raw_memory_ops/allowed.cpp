#include <cstddef>
#include <cstring>

struct Pair {
  int a = 0;
  int b = 0;
};

void copy_pair(Pair& dst, const Pair& src) {
  dst = src;
}

void copy_chars(char* dst, const char* src, std::size_t n) {
  std::memcpy(dst, src, n);
}

void clear_bytes(std::byte* dst, std::size_t n) {
  std::memset(dst, 0, n);
}
