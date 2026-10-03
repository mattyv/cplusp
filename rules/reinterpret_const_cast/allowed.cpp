#include <bit>
#include <cstdint>

float as_float(uint32_t bits) {
  return std::bit_cast<float>(bits);
}
