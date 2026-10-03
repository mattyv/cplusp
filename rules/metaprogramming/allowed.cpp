#include <cstdint>
#include <concepts>

template <std::integral T>
T twice(T x) {
  return x + x;
}

int32_t half(int32_t x) {
  return x / 2;
}

int64_t half(int64_t x) {
  return x / 2;
}
