#include <cstdint>
#include <variant>

// A variant of two types, decision 0202.
struct Point {
  int32_t x;
  int32_t y;
};

//@ requires std::holds_alternative<int32_t>(v)
//@ ensures result == std::get<int32_t>(v)
int32_t as_int(const std::variant<int32_t, bool>& v) {
  return std::get<int32_t>(v);
}

//@ ensures result == (std::holds_alternative<int32_t>(v) ? std::get<int32_t>(v) : 0)
int32_t int_or_zero(const std::variant<int32_t, bool>& v) {
  if (!std::holds_alternative<int32_t>(v)) {
    return 0;
  }
  return as_int(v);
}

//@ ensures result == (std::holds_alternative<bool>(v) && std::get<bool>(v))
bool is_true(std::variant<int32_t, bool> v) {
  return std::holds_alternative<bool>(v) && std::get<bool>(v);
}

// A contract names a type of 0064 only, so it says which alternative a variant of a struct holds through the other one.
//@ requires !std::holds_alternative<uint64_t>(v)
//@ ensures true
int32_t x_of(const std::variant<Point, uint64_t>& v) {
  return std::get<Point>(v).x;
}

// A variant parameter is an argument for a variant by value, as a copy, decision 0206.
//@ ensures result == (std::holds_alternative<bool>(v) && std::get<bool>(v))
bool calls_is_true(const std::variant<int32_t, bool>& v) {
  return is_true(v);
}
