#include <array>
#include <cstdint>
#include <memory>

namespace std {
struct Bag2 {
  std::array<int32_t, 2> a{};
  int32_t opened = 0;
};
inline const int32_t* begin(Bag2& b) {
  b.opened += 1;
  return &b.a[0];
}
inline const int32_t* end(Bag2& b) {
  return &b.a[0] + 2;
}
}  // namespace std

int32_t sum(const std::unique_ptr<std::Bag2>& p) {
  int32_t s = 0;
  for (int32_t x : *p) {
    s += x;
  }
  return s;
}
