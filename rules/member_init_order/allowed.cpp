#include <cstdint>

struct Pair {
  int32_t a;
  int32_t b;
  explicit Pair(int32_t x) : a(x + 1), b(x) {}
};

struct Triple {
  int32_t a = 0;
  int32_t b = 0;
  int32_t c = 0;
  explicit Triple(int32_t x) : a(x), b(x), c(x) {}
};
