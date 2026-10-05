#include <cstdint>
#include <type_traits>

// Trusted: the template is enabled for integral types only, by enable_if. The gate refuses SFINAE under the metaprogramming
// row, which is the point. Verified code sees only the plain contract of twice32 in example.cpp.
// The declaration in example.cpp carries the CPLUSP_TRUSTED marker.
template <typename T, typename = std::enable_if_t<std::is_integral_v<T>>>
T twice(T x) {
  return x + x;
}

int32_t twice32(int32_t x) {
  return twice(x);
}
