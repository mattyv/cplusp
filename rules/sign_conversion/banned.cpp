#include <cstddef>
#include <cstdint>
#include <vector>

uint32_t as_unsigned(int32_t i) {
  return i;  // BANNED
}

std::size_t as_index(int32_t i) {
  return i;  // BANNED
}

int32_t at(const std::vector<int32_t>& v, int32_t i) {
  return v[i];  // BANNED
}

std::size_t offset(std::size_t n, int32_t i) {
  return n + i;  // BANNED
}
