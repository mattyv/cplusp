#include <cstdint>
#include <utility>
#include <vector>

std::vector<int32_t> pass_on(std::vector<int32_t> items) {
  std::vector<int32_t> moved = std::move(items);
  return moved;
}

int32_t size_after_move() {
  std::vector<int32_t> a(3);
  const std::vector<int32_t> b = std::move(a);
  return static_cast<int32_t>(b.size());
}
