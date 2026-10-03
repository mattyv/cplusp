#include <utility>
#include <vector>

int use_after_move() {
  std::vector<int> a(3);
  std::vector<int> b = std::move(a);
  return static_cast<int>(a.size() + b.size());  // BANNED
}
