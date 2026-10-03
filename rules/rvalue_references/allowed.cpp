#include <utility>
#include <vector>

std::vector<int> pass_on(std::vector<int> items) {
  std::vector<int> moved = std::move(items);
  return moved;
}

int size_after_move() {
  std::vector<int> a(3);
  const std::vector<int> b = std::move(a);
  return static_cast<int>(b.size());
}
