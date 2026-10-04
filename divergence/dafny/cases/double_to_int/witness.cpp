// The edge where the naive model and the C++ part ways: 3e10 does not fit in int32_t.
// The conversion is undefined, and the sanitizer reports it.
#include <cstdint>
#include <cstdio>

int32_t whole(double x);

int main() {
  std::printf("%d\n", whole(3e10));
  return 0;
}
