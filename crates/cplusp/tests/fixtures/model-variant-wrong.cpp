#include <cstdint>
#include <variant>

// A read of an alternative that the variant may not hold fails, and so does a false claim, decision 0202.
//@ ensures true
int32_t read_any(const std::variant<int32_t, bool>& v) {
  return std::get<int32_t>(v);
}

//@ ensures result == std::holds_alternative<bool>(v)
bool holds_int(const std::variant<int32_t, bool>& v) {
  return std::holds_alternative<int32_t>(v);
}

//@ ensures result == std::get<bool>(v)
bool read_bool(const std::variant<int32_t, bool>& v) {
  return std::get<bool>(v);
}
