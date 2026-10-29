#include <cstdint>

// A static member function and a member function template of one name are overloads, so a contract cannot call that name, decision 0215.

struct S {
  int32_t a;

  //@ requires 0 <= x <= 100
  //@ ensures result == x + 1
  static int32_t get(int32_t x) { return x + 1; }

  //@ requires 0 <= a <= 100
  //@ ensures result == a + 2
  template <typename T>
  int32_t get(T x) const { return a + 2; }
};

//@ requires 0 <= s.a <= 100 && w == s.a
//@ ensures result == S::get(w) + 1
int32_t claim(const S& s, int64_t w) {
  return s.get(w);
}
