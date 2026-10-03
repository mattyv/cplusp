// The edge where the naive model and the C++ part ways: a call at run time has no compile-time check.
// The argument is volatile, so the compiler cannot evaluate the call while it compiles. 100000 * 100000 overflows.
// The definition is the same text as in code.cpp, because a constexpr function is defined in every file that calls it.
#include <cstdint>
#include <cstdio>

constexpr int32_t square(int32_t x) {
  return x * x;
}

int main() {
  volatile int32_t x = 100000;
  std::printf("%d\n", square(x));
  return 0;
}
