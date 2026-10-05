// The edge where the naive model and the C++ part ways: the moved-from string is empty, so s.size() is 0.
// Prints the result for "hi". The standard says only valid but unspecified. The libraries give 0.
// total_of_hi() builds the text inside, so one witness serves code.cpp, which holds a std::string, and fixed.cpp, which holds bytes.
#include <cstddef>
#include <cstdio>

std::size_t total_of_hi();

int main() {
  std::printf("%zu\n", total_of_hi());
  return 0;
}
