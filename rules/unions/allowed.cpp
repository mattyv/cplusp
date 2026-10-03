#include <cstdint>
#include <variant>

int64_t widen(const std::variant<int32_t, int64_t>& v) {
  if (std::holds_alternative<int64_t>(v)) {
    return std::get<int64_t>(v);
  }
  return std::get<int32_t>(v);
}
