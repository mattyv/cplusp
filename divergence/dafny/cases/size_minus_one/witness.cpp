// The edge where the naive model and the C++ part ways: an empty vector has size 0, and 0 - 1 wraps.
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <vector>

std::size_t last_index(const std::vector<int32_t>& v);

int main() {
  std::vector<int32_t> v;
  std::printf("%zu\n", last_index(v));
  return 0;
}
