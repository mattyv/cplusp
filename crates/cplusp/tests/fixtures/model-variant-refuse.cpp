#include <cstdint>
#include <variant>

// What a variant has no rule for yet, decision 0202.
//@ ensures true
bool three(const std::variant<int32_t, bool, uint64_t>& v) {
  return std::holds_alternative<bool>(v);
}

//@ ensures result == std::holds_alternative<int64_t>(v)
bool other(const std::variant<int32_t, bool>& v) {
  return std::holds_alternative<bool>(v);
}

//@ ensures true
bool second(const std::variant<int32_t, bool>& v) {
  return v.index() == 1;
}
