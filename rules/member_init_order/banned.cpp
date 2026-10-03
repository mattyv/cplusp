#include <cstdint>

struct Pair {
  int32_t a;
  int32_t b;
  explicit Pair(int32_t x) : b(x), a(x + 1) {}  // BANNED
};

struct Triple {
  int32_t a = 0;
  int32_t b = 0;
  int32_t c = 0;
  explicit Triple(int32_t x) : a(x), c(x), b(x) {}  // BANNED
};
