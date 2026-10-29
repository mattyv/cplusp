#include <cstdint>

struct S {
  int32_t a;

  //@ requires 0 <= x <= 100
  //@ ensures result == x + 1
  static int32_t get(int32_t x) { return x + 1; }

  //@ ensures result == 2
  int32_t get(int64_t x) {
    a = 1;
    return 2;
  }
};

// In C++, S::get(w) with an int64_t w picks the member get, which writes an object. So the line has no C++ meaning.
//@ requires 0 <= w <= 10
//@ ensures result == S::get(w) + 1
int32_t claim(int64_t w) {
  return static_cast<int32_t>(w) + 2;
}
