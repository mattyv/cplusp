#include <concepts>

template <std::integral T>
T twice(T x) {
  return x + x;
}

int half(int x) {
  return x / 2;
}

long half(long x) {
  return x / 2;
}
