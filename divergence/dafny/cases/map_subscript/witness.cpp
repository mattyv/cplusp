// The edge where the naive model and the C++ part ways: the key is not in the map.
// `m[k]` inserts it with the value 0. The result is 0, and the size after the call is 1.
// Prints the result and then the size.
#include <cstdint>
#include <cstdio>
#include <map>

int32_t value_or_zero(std::map<int32_t, int32_t>& m, int32_t k);

int main() {
  std::map<int32_t, int32_t> m;
  const int32_t r = value_or_zero(m, 7);
  std::printf("%d %zu\n", r, m.size());
  return 0;
}
