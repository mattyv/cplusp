#include <cstdint>
enum class Color { Red, Green };

int32_t code(Color c) {
  return c == Color::Red ? 1 : 2;
}
