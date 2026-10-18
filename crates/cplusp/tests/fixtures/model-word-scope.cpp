#include <cstdint>

// A name of a class, of a namespace or of a global variable that C++ finds from the function hides a contract word too, decision
// 0158. The check reads what C++ finds, so a function that finds no such name is no clash.
double eta = 5.0;

struct S {
  static constexpr double eps = 5.0;
  static constexpr double eta = 5.0;
  //@ ensures result > eps
  double f() const {
    return 1.0;
  }
  double f2() const;
};

//@ ensures result > eta
double S::f2() const {
  return 1.0;
}

namespace n {
constexpr double eps = 5.0;

//@ ensures result > eps
double g() {
  return 1.0;
}
}  // namespace n

//@ ensures result > eta
double h() {
  return 1.0;
}

//@ ensures result > eps
double clear() {
  return 1.0;
}

// C++ looks up the body of a friend that a class defines in that class.
struct F {
  static constexpr double eta = 5.0;
  //@ ensures result > eta
  friend double friendly() {
    return 1.0;
  }
};
