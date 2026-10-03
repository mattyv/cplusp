// The edge where the naive model and the C++ part ways: the literal 1 is an int, so 1 << 31 is INT32_MIN.
// C++20 defines it, then the result widens to a negative int64_t. At n = 32 the shift is undefined.
#include <cstdint>
#include <cstdio>

int64_t bit(uint32_t n);

int main() {
  std::printf("%lld\n", static_cast<long long>(bit(31)));
  return 0;
}
