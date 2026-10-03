#include <cstdint>

int64_t product(int32_t a, int32_t b) {
  return int64_t{a} * b;
}

int64_t area(int32_t w, int32_t h) {
  int64_t cells = static_cast<int64_t>(w) * h;
  return cells;
}

//@ requires -46340 <= a <= 46340
//@ requires -46340 <= b <= 46340
int32_t small_product(int32_t a, int32_t b) {
  return a * b;
}

uint64_t bytes(uint64_t n, uint64_t size) {
  return n * size;
}
