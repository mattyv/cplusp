// The edge where the naive model and the C++ part ways: the variant holds a bool.
// get_if returns a null pointer, and the read through it is undefined. The sanitizer reports the null read.
#include <cstdint>
#include <cstdio>
#include <variant>

int32_t as_int(const std::variant<int32_t, bool>& v);

int main() {
  std::variant<int32_t, bool> v{std::in_place_type<bool>, true};
  std::printf("%d\n", as_int(v));
  return 0;
}
