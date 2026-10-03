// The edge where the naive model and the C++ part ways: the index equals the size.
// The sanitizer sees the out-of-range subscript on a plain array. It does not see it on std::array.
#include <cstddef>
#include <cstdint>
#include <cstdio>

int32_t at(const int32_t (&a)[4], size_t i);

int main() {
  int32_t a[4] = {10, 20, 30, 40};
  std::printf("%d\n", at(a, 4));
  return 0;
}
