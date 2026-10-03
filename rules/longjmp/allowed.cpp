#include <optional>

std::optional<int> checked_half(int x) {
  if (x % 2 != 0) {
    return std::nullopt;
  }
  return x / 2;
}

int half_or_zero(int x) {
  return checked_half(x).value_or(0);
}
