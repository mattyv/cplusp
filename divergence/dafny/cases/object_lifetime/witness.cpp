// The edge where the naive model and the C++ part ways: the read comes after `local` has gone out of scope.
// The sanitizer reports a use of stack memory after its scope. Without it the program usually prints 42.
#include <cstdint>
#include <cstdio>

int32_t read_later();

int main() {
  std::printf("%d\n", read_later());
  return 0;
}
