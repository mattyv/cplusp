// The sum overflows int, which is undefined behaviour. The naive model proves the comparison true.
#include <cstdio>

bool positive();

int main() {
  std::printf("%d\n", positive() ? 1 : 0);
  return 0;
}
