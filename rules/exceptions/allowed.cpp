#include <optional>

std::optional<int> parse(int x) {
  if (x < 0) {
    return std::nullopt;
  }
  return x;
}

int parse_or_zero(int x) {
  return parse(x).value_or(0);
}
