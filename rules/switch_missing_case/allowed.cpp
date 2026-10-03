#include <cstdint>

enum class Mode : uint8_t { Fast, Slow };

int32_t pick(Mode m) {
  switch (m) {
    case Mode::Fast:
      return 1;
    case Mode::Slow:
      return 2;
  }
  return 0;
}

int32_t steps(int32_t k) {
  switch (k) {
    case 1:
      return 1;
    case 2:
      return 2;
    default:
      return 0;
  }
}
