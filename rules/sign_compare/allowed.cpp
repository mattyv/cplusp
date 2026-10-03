#include <cstddef>
#include <cstdint>
#include <utility>

bool below(int32_t i, std::size_t n) {
  return i < 0 || static_cast<std::size_t>(i) < n;
}

bool below_std(int32_t i, std::size_t n) {
  return std::cmp_less(i, n);
}

bool short_limit(std::size_t n) {
  return n < 3;
}

bool promoted(uint8_t a, int32_t b) {
  return a < b;
}

bool widened(int64_t l, uint32_t u) {
  return l < u;
}
