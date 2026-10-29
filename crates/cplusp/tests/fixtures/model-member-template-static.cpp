#include <cstdint>

// A static member function template has no rule yet, decision 0215.

struct One {
  int32_t n;
};

struct S {
  int32_t a;
  //@ requires 0 <= v.n <= 10
  //@ ensures result == v.n + 1
  template <typename T> static int32_t up(T v) { return v.n + 1; }
};

//@ ensures result == 3
int32_t demo() { return S::up(One{2}); }
