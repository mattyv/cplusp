#include <cstdint>

int64_t bit(uint32_t n) {
  return 1 << n;  // BANNED
}

int64_t mask(uint32_t n) {
  return (1 << n) - 1;  // BANNED
}

int32_t flag(uint32_t n) {
  return 1 << n;  // BANNED
}
