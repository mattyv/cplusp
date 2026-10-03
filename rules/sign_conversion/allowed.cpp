#include <cstddef>
#include <cstdint>
#include <vector>

//@ requires i >= 0
std::size_t as_index(int32_t i) {
  return static_cast<std::size_t>(i);
}

//@ requires 0 <= i < 4
int32_t at(const std::vector<int32_t>& v, int32_t i) {
  return v[static_cast<std::size_t>(i)];
}

std::size_t plus_one(std::size_t n) {
  return n + 1;
}

int64_t widened(uint32_t u) {
  return u;
}

bool below(int32_t i, std::size_t n) {
  return i < 0 || static_cast<std::size_t>(i) < n;
}

bool nonzero(int32_t x) {
  return x;
}

enum class Level : uint8_t { Low = 1, High = 2 };
