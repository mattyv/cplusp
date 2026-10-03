#include <cstdint>
#include <optional>

//@ ensures result == *opt
int32_t value(const std::optional<int32_t>& opt) {
  return *opt;
}
