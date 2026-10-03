#include <array>
#include <cstddef>
#include <cstdint>

//@ ensures result == a[i]
int32_t at(const std::array<int32_t, 4>& a, std::size_t i) {
  return a[i];
}
