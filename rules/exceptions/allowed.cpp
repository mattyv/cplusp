#include <cstdint>
#include <optional>

std::optional<int32_t> parse(int32_t x) {
  if (x < 0) {
    return std::nullopt;
  }
  return x;
}

int32_t parse_or_zero(int32_t x) {
  return parse(x).value_or(0);
}
