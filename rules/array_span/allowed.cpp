#include <array>
#include <cstdint>
#include <span>
#include <vector>

//@ requires s.size() > 0
int32_t first(std::span<const int32_t> s) {
  return s[0];
}

int32_t first_of(const std::vector<int32_t>& v) {
  return first(v);
}

int32_t last_of_four(const std::array<int32_t, 4>& a) {
  return a[3];
}
