#include <array>
#include <cstdint>
#include <span>

const int32_t& in_span() {
  std::array<int32_t, 2> a{1, 2};
  std::span<const int32_t> s = a;
  return s[0];
}

const int32_t& in_pointer() {
  int32_t local = 1;
  const int32_t* p = &local;
  return *p;
}
