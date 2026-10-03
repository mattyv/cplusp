#include <cstdint>
#include <optional>

//@ ensures result == (o.has_value() && *o == 5)
bool is_five(const std::optional<int32_t>& o) {
  return o == 5;
}

//@ ensures result == (!o.has_value() || *o < 5)
bool below_five(const std::optional<int32_t>& o) {
  return o < 5;
}
