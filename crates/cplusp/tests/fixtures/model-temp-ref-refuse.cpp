#include <cstdint>

// A temporary in the return of a function that returns a reference dies before the caller reads it, decision 0181.
struct Pair {
  int32_t a;
  int32_t b;
};

//@ ensures result.a == p.a
const Pair& same(const Pair& p) {
  return p;
}

//@ ensures result.a == 1
const Pair& dangles() {
  return same(Pair{1, 2});
}

struct Outer {
  Pair in;

  //@ ensures result.a == in.a
  const Pair& inner() const { return in; }
};

//@ ensures result.in.a == 1
Outer make() {
  return Outer{Pair{1, 2}};
}

//@ ensures result.a == 1
const Pair& dangles_too() {
  return make().inner();
}

// A temporary of a class over an interface, at a parameter of the interface, keeps its refusal. The cast to the interface stays.
struct Shape {
  virtual ~Shape() = default;
  //@ ensures result >= 0
  virtual int32_t corners() const = 0;
};

class Square final : public Shape {
 public:
  //@ ensures result == 4
  int32_t corners() const override { return 4; }
};

//@ ensures result >= 0
int32_t count(const Shape& s) {
  return s.corners();
}

//@ ensures result >= 0
int32_t square() {
  return count(Square{});
}
