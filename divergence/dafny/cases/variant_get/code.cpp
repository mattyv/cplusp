#include <cstdint>
#include <variant>

//@ ensures result == the int32_t in v
int32_t as_int(const std::variant<int32_t, bool>& v) {
  return *std::get_if<int32_t>(&v);
}
