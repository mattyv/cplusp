#include <cstdint>

enum class Mode : uint8_t { Fast, Slow };

//@ ensures result == (v == 0 ? Mode::Fast : Mode::Slow)
Mode to_mode(uint8_t v) {
  return static_cast<Mode>(v);
}
