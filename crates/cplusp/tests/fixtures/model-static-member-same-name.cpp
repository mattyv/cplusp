#include <cstdint>

// A static member function and a member function of one name are two functions of that name, so a contract cannot call it, decisions 0095 and 0216.
struct S {
  int32_t a;

  //@ requires 0 <= x <= 100
  //@ ensures result == x + 1
  static int32_t get(int32_t x) { return x + 1; }

  //@ requires 0 <= a <= 100
  //@ ensures result == a + 2
  int32_t get(int64_t x) const { return a + 2; }
};

// In C++, s.get(x) with an int32_t x calls the static get, which gives x + 1. The claim is false for s.a == 0 and x == 0.
//@ requires 0 <= s.a <= 100 && 0 <= x <= 100
//@ ensures result == s.get(x)
int32_t member_call(const S& s, int32_t x) {
  return s.a + 2;
}

// In C++, S::get(w) with an int64_t w picks the member get, which needs an object.
//@ requires 0 <= s.a <= 100 && w == s.a
//@ ensures result == S::get(w) + 1
int32_t static_call(const S& s, int64_t w) {
  return s.get(w);
}
