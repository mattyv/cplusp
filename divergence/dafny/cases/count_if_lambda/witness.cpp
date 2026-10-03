// The edge where the model and the C++ agree: the lambda counts the elements above k, as the model says.
// Prints the count for {1, 5, 3} and 2.
#include <cstdint>
#include <cstdio>
#include <vector>

int64_t above(const std::vector<int32_t>& v, int32_t k);

int main() {
  std::vector<int32_t> v = {1, 5, 3};
  std::printf("%lld\n", static_cast<long long>(above(v, 2)));
  return 0;
}
