#include <optional>

int value_or_zero(const std::optional<int>& v) {
  return v.value_or(0);
}

std::optional<int> make(int x) {
  std::optional<int> v;
  v.emplace(x);
  return v;
}
