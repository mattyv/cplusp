#include <cstdint>
// A qualified call of a static member function in a contract of a member function takes no object, decision 0225.
struct S {
  int32_t a;

  //@ requires 0 <= x <= 100
  //@ ensures result == x + 1
  static int32_t get(int32_t x) { return x + 1; }

  // S::get(w) is the static function, so the claim is result == w + 2, which holds.
  //@ requires 0 <= a <= 100 && w == a
  //@ ensures result == S::get(w) + 1
  int32_t h(int64_t w) const { return a + 2; }
};

//@ requires 0 <= s.a <= 100 && w == s.a
//@ ensures result == S::get(w) + 1
int32_t claim(const S& s, int64_t w) {
  return s.a + 2;
}
