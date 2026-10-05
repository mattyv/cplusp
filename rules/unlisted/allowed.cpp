#include <cstddef>
#include <cstdint>
#include <optional>
#include <vector>

// Ordinary code: every kind of node here is on the lists of the row.
struct Point {
  int32_t x = 0;
  int32_t y = 0;
};

//@ requires -0x40000000 <= p.x < 0x40000000 && -0x40000000 <= p.y < 0x40000000
//@ ensures result == p.x + p.y
int32_t sum(const Point& p) {
  return p.x + p.y;
}

//@ ensures result.has_value() == (v.size() > 0)
std::optional<int32_t> first(const std::vector<int32_t>& v) {
  if (v.empty()) {
    return std::nullopt;
  }
  return v[0];
}

//@ ensures result <= v.size()
std::size_t count_positive(const std::vector<int32_t>& v) {
  std::size_t n = 0;
  for (const int32_t x : v) {
    if (x > 0) {
      ++n;
    }
  }
  return n;
}
