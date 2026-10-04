#include <bit>
#include <cstdint>

double as_double(uint64_t bits) {
  return std::bit_cast<double>(bits);
}
