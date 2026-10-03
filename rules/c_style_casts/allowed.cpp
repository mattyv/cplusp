#include <cstdint>

int32_t narrow(int64_t big) {
  return static_cast<int32_t>(big);
}
