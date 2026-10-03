// The edge where the naive model and the C++ part ways: a depth of ten million frames does not fit in the stack.
// The sanitizer reports the stack overflow.
#include <cstdint>
#include <cstdio>

int32_t depth(int32_t n);

int main() {
  std::printf("%d\n", depth(10000000));
  return 0;
}
