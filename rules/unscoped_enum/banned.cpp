#include <cstdint>
enum Color { Red, Green };  // BANNED

enum Mode : uint32_t { Fast, Slow };  // BANNED

enum { Mask = 3 };  // BANNED

int32_t code(Color c) {
  return c == Red ? Mask : Fast;
}
