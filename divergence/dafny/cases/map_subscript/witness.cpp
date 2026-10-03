// The edge where the naive model and the C++ part ways: the key is not in the map.
// `m[k]` inserts it with the value 0. The size is then 1, and the result is 1.
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <map>

std::size_t count_after_read(std::map<int32_t, int32_t>& m, int32_t k);

int main() {
  std::map<int32_t, int32_t> m;
  std::printf("%zu\n", count_after_read(m, 7));
  return 0;
}
