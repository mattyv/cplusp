#include <cstdint>

// A call of a plain member function is its function in place, decision 0189.
struct Negate {
  //@ ensures result == true
  bool valid() const { return true; }

  //@ requires -1000000 <= x && x <= 1000000
  //@ ensures result == -x
  int32_t apply(int32_t x) const { return -x; }
};

// A class that calls the plain member functions of its field is pure itself.
class Twice {
 public:
  //@ ensures result == step_.valid()
  bool valid() const { return step_.valid(); }

  //@ requires valid() && -1000000 <= x && x <= 1000000
  //@ ensures result == step_.apply(step_.apply(x))
  int32_t run(int32_t x) const { return step_.apply(step_.apply(x)); }

 private:
  Negate step_;
};

// A call of a plain member function of its own class.
struct Pair {
  int32_t a = 0;
  int32_t b = 0;

  //@ requires -1000 <= a && a <= 1000
  //@ ensures result == a
  int32_t first() const { return a; }

  //@ requires -1000 <= a && a <= 1000
  //@ ensures result == 2 * a
  int32_t twice() const { return first() + first(); }
};

//@ requires t.valid() && -1000000 <= x && x <= 1000000
//@ ensures result == x
int32_t back(const Twice& t, int32_t x) {
  return t.run(x);
}

// The call stands on the right of && and in a branch of ?:.
//@ requires -1000 <= p.a && p.a <= 1000
//@ ensures result == (p.a > 0 ? 2 * p.a : 0)
int32_t pick(const Pair& p) {
  return p.a > 0 && p.first() > 0 ? p.twice() : 0;
}
