#include <cstdint>

enum class Mode : uint8_t { Fast, Slow };

//@ ensures result == (v == 0 ? Mode::Fast : Mode::Slow)
Mode to_mode(uint8_t v) {
  if (v == 0) {
    return Mode::Fast;
  }
  return Mode::Slow;
}
