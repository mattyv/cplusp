#include <cstdint>
template <typename T>
T twice(T x) {
  return x + x;
}

template <typename T>
struct Box {
  T value;
};

int32_t use() {
  Box<int32_t> b{twice(2)};
  return b.value;
}
