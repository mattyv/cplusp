// The edge where the naive model and the C++ part ways: the unique_ptr deletes a Derived through a Base.
// Base has no virtual destructor, so the sanitizer reports the delete, and the string in Derived leaks.
#include <cstdint>
#include <cstdio>

int32_t value_of_new();

int main() {
  std::printf("%d\n", value_of_new());
  return 0;
}
