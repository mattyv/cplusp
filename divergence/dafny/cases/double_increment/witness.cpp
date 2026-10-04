// The edge where the naive model and the C++ part ways: above 2^53 the doubles are 2 apart.
// The exact sum 2^53 + 1 is halfway between two doubles, and it rounds to the even one, 2^53.
#include <cstdio>

double next(double x);

int main() {
  std::printf("%d\n", next(9007199254740992.0) == 9007199254740992.0);
  return 0;
}
