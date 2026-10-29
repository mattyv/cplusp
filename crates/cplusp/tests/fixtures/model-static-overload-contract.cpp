#include <cstdint>

// Two static member functions of one name are overloads, so a contract cannot call that name, decision 0215.

struct S {
  int32_t a;

  //@ requires 0 <= x <= 100
  //@ ensures result == x + 1
  static int32_t get(int32_t x) { return x + 1; }

  //@ requires 0 <= x <= 100
  //@ ensures result == x + 2
  static int32_t get(int64_t x) { return static_cast<int32_t>(x) + 2; }
};

//@ requires 0 <= w <= 100
//@ ensures result == S::get(w) + 1
int32_t claim(int64_t w) {
  return S::get(w);
}
