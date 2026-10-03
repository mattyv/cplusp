// The edge where the naive model and the C++ part ways: two values of INT32_MAX in an int64_t vector.
// The fold runs in int. The second sum, 4294967294, is narrowed to int and wraps to -2. C++20 defines the wrap.
#include <cstdint>
#include <cstdio>
#include <vector>

int64_t total(const std::vector<int64_t>& v);

int main() {
  std::vector<int64_t> v = {INT32_MAX, INT32_MAX};
  std::printf("%lld\n", static_cast<long long>(total(v)));
  return 0;
}
