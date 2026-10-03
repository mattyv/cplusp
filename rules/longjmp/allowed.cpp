#include <cstdint>
#include <optional>

std::optional<int32_t> checked_half(int32_t x) {
  if (x % 2 != 0) {
    return std::nullopt;
  }
  return x / 2;
}

int32_t half_or_zero(int32_t x) {
  return checked_half(x).value_or(0);
}
