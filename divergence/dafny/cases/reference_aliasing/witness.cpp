// The edge where the naive model and the C++ part ways: add_both(x, x) is one object, not two.
// code.cpp prints the aliased result, 12. fixed.cpp passes two objects and prints 7 and 11, as the contract says.
#include <cstdint>
#include <cstdio>

int32_t demo();

int main() {
  int32_t r = demo();
  if (r > 99) {
    std::printf("%d %d\n", r / 100, r % 100);
  } else {
    std::printf("%d\n", r);
  }
  return 0;
}
