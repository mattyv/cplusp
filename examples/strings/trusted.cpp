#include <cstddef>
#include <cstdint>
#include <string>

size_t decimal_width(int32_t n) {
  std::string digits = std::to_string(n);
  return digits.size();
}
