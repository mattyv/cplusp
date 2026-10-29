#include <cstdint>

// A member function template counts as an overload of its name, so a contract cannot call that name, decision 0215.

struct S {
  int32_t a;
  //@ requires 0 <= a <= 100
  //@ ensures result == a + 1
  int32_t get(int32_t x) const { return a + 1; }
  //@ requires 0 <= a <= 100
  //@ ensures result == a + 2
  template <typename T> int32_t get(T x) const { return a + 2; }
};

//@ requires 0 <= s.a <= 100 && 0 <= w <= 10
//@ ensures result == s.get(w) + 1
int32_t claim(const S& s, int64_t w) { return s.get(w); }
