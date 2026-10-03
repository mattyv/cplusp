// The edge where the naive model and the C++ part ways: the pointer is null, and the read goes through it.
// The sanitizer reports the null dereference.
#include <cstdint>
#include <cstdio>

int32_t read(const int32_t* p);

int main() {
  std::printf("%d\n", read(nullptr));
  return 0;
}
