#include <array>
#include <cstdint>

constexpr int32_t limit = 5;

constinit int32_t count = 0;

int32_t zero = 0;

constexpr std::array<int32_t, 2> table{1, 2};

int32_t five() {
  return limit;
}
