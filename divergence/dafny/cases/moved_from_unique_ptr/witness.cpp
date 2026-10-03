// The edge where the naive model and the C++ part ways: after the move, p holds nullptr, and `*p` reads through it.
// The sanitizer reports the null dereference. Prints the result for a value of 7, when the program reaches it.
#include <cstdint>
#include <cstdio>
#include <memory>

int32_t take(std::unique_ptr<int32_t> p);

int main() {
  std::printf("%d\n", take(std::make_unique<int32_t>(7)));
  return 0;
}
