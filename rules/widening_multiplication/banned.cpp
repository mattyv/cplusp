#include <cstdint>

int64_t product(int32_t a, int32_t b) {
  return a * b;  // BANNED
}

int64_t area(int32_t w, int32_t h) {
  int64_t cells = w * h;  // BANNED
  return cells;
}

uint64_t bytes(uint32_t n, uint32_t size) {
  return n * size;  // BANNED
}
