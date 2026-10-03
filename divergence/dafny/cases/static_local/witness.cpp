// The edge where the naive model and the C++ part ways: n is one object that keeps its value between calls.
// The first call returns 1, and the second call returns 2.
#include <cstdint>
#include <cstdio>

int32_t counter();

int main() {
  int32_t first = counter();
  int32_t second = counter();
  std::printf("%d %d\n", first, second);
  return 0;
}
