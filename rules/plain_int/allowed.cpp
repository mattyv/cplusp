#include <array>
#include <cstddef>
#include <cstdint>

int32_t twice(int32_t x) {
  return 2 * x;
}

int8_t narrow(int64_t x) {
  return static_cast<int8_t>(x);
}

uint32_t first(const std::array<uint32_t, 4>& table) {
  return table[0];
}

std::size_t count(const std::array<uint32_t, 4>& table) {
  return table.size();
}

bool is_set(bool flag) {
  return flag;
}

enum class Mode : uint8_t { Fast, Slow };

#include <vector>

int32_t count(const std::vector<int32_t>& v) {
  const auto n = v.size();
  return static_cast<int32_t>(n);
}
