#include <cstdint>
#include <span>
#include <vector>

int32_t first_after_grow(std::vector<int32_t>& v) {
  std::span<int32_t> s = v;  // BANNED
  v.push_back(1);
  return s[0];
}

struct View {
  std::span<const int32_t> window;  // BANNED
};
