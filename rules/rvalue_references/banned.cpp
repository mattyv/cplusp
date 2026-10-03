#include <cstdint>
#include <utility>
#include <vector>

int32_t use_after_move() {
  std::vector<int32_t> a(3);
  std::vector<int32_t> b = std::move(a);
  return static_cast<int32_t>(a.size() + b.size());  // BANNED
}
