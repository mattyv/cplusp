// The edge where the naive model and the C++ part ways: the string has no 'z'.
// `find` returns npos, which is size_t(-1), and npos + 1 wraps to 0.
#include <cstddef>
#include <cstdio>
#include <string>

std::size_t after(const std::string& s);

int main() {
  std::printf("%zu\n", after("abc"));
  return 0;
}
