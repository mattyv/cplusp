#include <cstdint>

// A name with a character that Dafny cannot read is refused, decision 0069. Clang accepts `$` in a name.
int32_t dollar(int32_t x) {
  int32_t a$b = x;
  return a$b;
}
