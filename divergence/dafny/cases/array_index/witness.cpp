// The edge where the naive model and the C++ part ways: the index equals the size.
// The sanitizer sees this read, because the std::array is on the stack. It does not see it on a heap vector.
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>

int32_t at(const std::array<int32_t, 4>& a, std::size_t i);

int main() {
  std::array<int32_t, 4> a = {10, 20, 30, 40};
  std::printf("%d\n", at(a, 4));
  return 0;
}
