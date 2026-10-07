#include <array>
#include <cstdint>
#include <memory>

struct Bag {
  std::array<int32_t, 2> a{};
  int32_t opened = 0;
  std::array<int32_t, 2>::const_iterator begin() {
    opened += 1;
    return a.cbegin();
  }
  std::array<int32_t, 2>::const_iterator end() const {
    return a.cend();
  }
};

int32_t sum(const std::unique_ptr<Bag>& p) {
  int32_t s = 0;
  for (int32_t x : *p) {
    s += x;
  }
  return s;
}
