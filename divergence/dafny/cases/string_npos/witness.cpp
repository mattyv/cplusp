// The edge where the naive model and the C++ part ways: the text has no 'z'.
// `find` returns npos, which is size_t(-1), and npos + 1 wraps to 0.
// after_z() builds the text "abc" inside, so one witness serves code.cpp, which holds a std::string, and fixed.cpp, which holds bytes.
#include <cstddef>
#include <cstdio>

std::size_t after_z();

int main() {
  std::printf("%zu\n", after_z());
  return 0;
}
