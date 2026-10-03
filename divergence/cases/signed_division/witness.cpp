// The edge where the naive model and the C++ part ways: -7 / 2 is -3 in C++ and -4 in Dafny.
#include <cstdint>
#include <cstdio>

int32_t quot(int32_t a, int32_t b);
int32_t rem(int32_t a, int32_t b);

int main() {
  std::printf("%d %d\n", quot(-7, 2), rem(-7, 2));
  return 0;
}
