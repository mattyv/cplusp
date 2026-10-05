#include <cstdint>

int32_t narrow(int64_t big) {
  return static_cast<int32_t>(big);
}

// Braces cannot narrow, so a braced functional cast is fine.
int64_t widen_braced(int32_t x) {
  return int64_t{x};
}
