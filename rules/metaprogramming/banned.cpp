#include <type_traits>

template <typename T, typename = std::enable_if_t<std::is_integral_v<T>>>  // BANNED
T twice(T x) {
  return x + x;
}

template <typename T> typename std::enable_if<std::is_integral<T>::value, T>::type half(T x) { return x / 2; }  // BANNED

template <typename T>
using Wide = std::conditional_t<(sizeof(T) < 8), long, T>;  // BANNED

template <typename T>
struct Tag {
  using type = std::void_t<T>;  // BANNED
};
