#include <cstdint>
// A static member function named by its class inside a namespace is the function of the file, decision 0225.
namespace ns {
struct T {
  int32_t a;

  //@ requires 0 <= x <= 100
  //@ ensures result == x + 1
  static int32_t up(int32_t x) { return x + 1; }
};

//@ requires 0 <= x <= 100
//@ ensures result == T::up(x)
int32_t one(int32_t x) {
  const T t{1};
  return T::up(x);
}
}  // namespace ns

//@ requires 0 <= x <= 100
//@ ensures result == ns::T::up(x)
int32_t two(int32_t x) {
  return ns::T::up(x);
}
