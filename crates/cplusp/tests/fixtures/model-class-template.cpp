#include <cstdint>

// A class template is a struct for each type that the file uses it at, decision 0188.
template <typename T>
class Box {
 public:
  //@ ensures get() == v
  explicit Box(T v) : v_(v) {}

  //@ ensures result == v_
  T get() const { return v_; }

  //@ ensures get() == v
  void set(T v) { v_ = v; }

 private:
  T v_;
};

// An explicit instantiation makes the body of each member function.
template class Box<int32_t>;
template class Box<bool>;

struct Point {
  int32_t x;
  int32_t y;
};

// Two type parameters, and a struct as a type argument.
template <typename A, typename B>
struct Pair {
  A first;
  B second;
};

//@ ensures result == 7
int32_t seven() {
  Box<int32_t> b(3);
  b.set(7);
  return b.get();
}

//@ ensures result == true
bool yes() {
  Box<bool> b(false);
  b.set(true);
  return b.get();
}

//@ ensures result == 5
int32_t pair_of() {
  const Pair<Point, bool> p{Point{5, 6}, true};
  return p.first.x;
}
