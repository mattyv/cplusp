#include <cstdint>

enum class Mode : uint8_t { Fast, Slow };

//@ ensures result == (m == Mode::Fast ? 1 : 2)
int32_t pick(Mode m) {
  switch (m) {
    case Mode::Fast:
      return 1;
    case Mode::Slow:
      return 2;
  }
  return 0;
}
