// The edge where the naive model and the C++ part ways: the constructor writes b first, and the members are
// initialized in declaration order, so a gets the first value. Prints a and b.
// The witness sees the layout of Pair only. It never calls the constructor.
#include <cstdint>
#include <cstdio>

struct Pair {
  int32_t a;
  int32_t b;
};

Pair make();

int main() {
  Pair p = make();
  std::printf("%d %d\n", p.a, p.b);
  return 0;
}
