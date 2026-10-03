// The edge where the naive model and the C++ part ways: -1 becomes the largest size_t, so it is not below 1.
#include <cstddef>
#include <cstdint>
#include <cstdio>

bool below(int32_t i, size_t n);

int main() {
  std::printf("%d\n", below(-1, 1));
  return 0;
}
