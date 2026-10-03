// The edge where the naive model and the C++ part ways: 100000 * 100000 is computed in int32_t, and it does not fit.
#include <cstdint>
#include <cstdio>

int64_t product(int32_t a, int32_t b);

int main() {
  std::printf("%lld\n", static_cast<long long>(product(100000, 100000)));
  return 0;
}
