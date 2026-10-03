// The edge where the naive model and the C++ part ways: true + true is 2, because both operands become int.
#include <cstdint>
#include <cstdio>

int32_t count_true(bool a, bool b);

int main() {
  std::printf("%d\n", count_true(true, true));
  return 0;
}
