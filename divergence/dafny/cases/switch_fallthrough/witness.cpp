// The edge where the naive model and the C++ part ways: k is 1.
// Case 1 has no break, so control runs into case 2. The result is 1 + 2.
#include <cstdint>
#include <cstdio>

int32_t steps(int32_t k);

int main() {
  std::printf("%d\n", steps(1));
  return 0;
}
