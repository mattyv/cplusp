#include <cstdint>
#include <optional>

int32_t value_or_zero(const std::optional<int32_t>& v) {
  return v.value_or(0);
}

std::optional<int32_t> make(int32_t x) {
  std::optional<int32_t> v;
  v.emplace(x);
  return v;
}
