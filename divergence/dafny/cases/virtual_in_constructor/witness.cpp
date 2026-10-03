// The edge where the naive model and the C++ part ways: the constructor of Base calls kind() while the object is
// still a Base, so it gets 1, not the 2 of Derived.
#include <cstdint>
#include <cstdio>

int32_t seen_kind();

int main() {
  std::printf("%d\n", seen_kind());
  return 0;
}
