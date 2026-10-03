// The edge where the naive model and the C++ part ways: the moved-from string is empty, so s.size() is 0.
// Prints the result for "hi". The standard says only valid but unspecified. The libraries give 0.
#include <cstddef>
#include <cstdio>
#include <string>

std::size_t total(std::string s);

int main() {
  std::printf("%zu\n", total("hi"));
  return 0;
}
