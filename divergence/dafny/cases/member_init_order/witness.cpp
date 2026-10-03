// The edge where the naive model and the C++ part ways: the constructor writes b first, and the members are
// initialized in declaration order, so a gets the first value. Prints a and b.
// The struct is the text of Pair in code.cpp, so the definitions agree. The witness never calls the constructor.
// fixed.cpp swaps the two mem-initializers, and the witness is linked with it too.
#include <cstdint>
#include <cstdio>

int32_t next(int32_t& counter);

struct Pair {
  int32_t a;
  int32_t b;

  //@ requires counter <= 0x7FFFFFF0
  //@ modifies counter
  //@ ensures b == old(counter) + 1 && a == old(counter) + 2
  explicit Pair(int32_t& counter) : b(next(counter)), a(next(counter)) {}
};

Pair make();

int main() {
  Pair p = make();
  std::printf("%d %d\n", p.a, p.b);
  return 0;
}
