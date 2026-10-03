#include <cstddef>
#include <cstdint>
#include <vector>

bool below(int32_t i, std::size_t n) {
  return i < n;  // BANNED
}

bool same(uint32_t u, int32_t i) {
  return u == i;  // BANNED
}

bool in_range(int32_t i, const std::vector<int32_t>& v) {
  return i < v.size();  // BANNED
}

bool negative_limit(std::size_t n) {
  return n < -3;  // BANNED
}
