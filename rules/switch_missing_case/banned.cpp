#include <cstdint>

enum class Mode : uint8_t { Fast, Slow };

int32_t pick(Mode m) {
  switch (m) {  // BANNED
    case Mode::Fast:
      return 1;
  }
  return 0;
}

int32_t steps(int32_t k) {
  switch (k) {  // BANNED
    case 1:
      return 1;
    case 2:
      return 2;
  }
  return 0;
}
