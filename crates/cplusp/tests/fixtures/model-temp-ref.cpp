#include <cstdint>

// A temporary of a plain struct, bound to a `const T&` parameter, is its value, decision 0181.
struct Pair {
  int32_t a;
  int32_t b;

  //@ requires -1000 < a && a < 1000 && -1000 < b && b < 1000
  //@ ensures result == a + b
  int32_t sum() const { return a + b; }
};

//@ requires p.a < 1000 && p.b < 1000 && -1000 < p.a && -1000 < p.b
//@ ensures result == p.a + p.b
int32_t total(const Pair& p) {
  return p.sum();
}

//@ ensures result == 3
int32_t brace() {
  return total(Pair{1, 2});
}

//@ requires -100 < x && x < 100
//@ ensures result == x + x + 7
int32_t in_local(int32_t x) {
  int32_t t = total(Pair{x, x});
  return t + 7;
}

//@ requires -100 < x && x < 100
//@ ensures result == 2 * x + 1
int32_t twice(int32_t x) {
  return total(Pair{x, x}) + total(Pair{1, 0});
}

// A brace list keeps the order of the fields.
//@ requires p.a < 1000 && p.b < 1000 && -1000 < p.a && -1000 < p.b
//@ ensures result == p.a - p.b
int32_t gap(const Pair& p) {
  return p.a - p.b;
}

//@ ensures result == -1
int32_t ordered() {
  return gap(Pair{1, 2});
}

// Two temporaries in one call.
//@ requires p.a < 1000 && q.a < 1000 && -1000 < p.a && -1000 < q.a
//@ ensures result == p.a - q.a
int32_t apart(const Pair& p, const Pair& q) {
  return p.a - q.a;
}

//@ ensures result == -2
int32_t both() {
  return apart(Pair{1, 0}, Pair{3, 0});
}

// The value of a call that gives the struct.
//@ requires -100 < x && x < 100
//@ ensures result.a == x && result.b == x + 1
Pair make(int32_t x) {
  return Pair{x, x + 1};
}

//@ requires -100 < x && x < 100
//@ ensures result == -1
int32_t from_call(int32_t x) {
  return gap(make(x));
}

// A call of a constructor.
struct Cell {
  int32_t v;

  //@ ensures v == x
  explicit Cell(int32_t x) : v(x) {}
};

//@ ensures result == c.v
int32_t read(const Cell& c) {
  return c.v;
}

//@ ensures result == 4
int32_t built() {
  return read(Cell(4));
}

// A destructor `= default` is no destructor of the model, decision 0179.
struct Flat {
  int32_t v;
  ~Flat() = default;
};

//@ ensures result == f.v
int32_t flat(const Flat& f) {
  return f.v;
}

//@ ensures result == 5
int32_t defaulted() {
  return flat(Flat{5});
}
