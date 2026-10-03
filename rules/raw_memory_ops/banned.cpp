#include <cstdint>
#include <cstddef>
#include <cstring>

struct Pair {
  int32_t a = 0;
  int32_t b = 0;
};

void copy_pair(Pair& dst, const Pair& src) {
  std::memcpy(&dst, &src, sizeof(Pair));  // BANNED
}

void clear_pair(Pair& dst) {
  std::memset(&dst, 0, sizeof(Pair));  // BANNED
}

void move_pair(Pair& dst, const Pair& src) {
  std::memmove(&dst, &src, sizeof(Pair));  // BANNED
}

void copy_pair_global(Pair& dst, const Pair& src) {
  memcpy(&dst, &src, sizeof(Pair));  // BANNED
}
