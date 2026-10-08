// The size of a vector always fits size_t. The naive model cannot show that, so it refuses code that is fine.
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <vector>

size_t count(const std::vector<int32_t>& v);

int main() {
  std::printf("%zu\n", count(std::vector<int32_t>{4, 5, 6}));
  return 0;
}
