#include <cstdint>

// Overloads and the same name in two namespaces are different functions, each with its own method, decision 0058. If the translator
// took one for the other, a contract below would fail.
namespace n {
//@ ensures result == 1
int32_t d() {
  return 1;
}
}  // namespace n

//@ ensures result == 2
int32_t d() {
  return 2;
}

//@ ensures result == 3
int32_t both() {
  int32_t one = n::d();
  int32_t two = d();
  return one + two;
}

//@ requires x < 100
//@ ensures result == x + 1
int32_t b(int32_t x) {
  return x + 1;
}

//@ requires x < 100
//@ ensures result == x + 2
int64_t b(int64_t x) {
  return x + 2;
}

//@ ensures result == 6
int32_t calls_b32() {
  return b(5);
}

//@ ensures result == 7
int64_t calls_b64() {
  return b(int64_t{5});
}
