#include <cstdint>
#include <utility>

// A std::move of a trivially copyable value is the value, and the source keeps it. A constructor template has an instance for
// each type that the file makes it with, decision 0212. False claims fail.
struct Square {
  int32_t side;
};

class Holder {
 public:
  //@ ensures value() == s.side
  explicit Holder(Square s) : s_(std::move(s)) {}

  //@ ensures result == s_.side
  int32_t value() const { return s_.side; }

 private:
  Square s_;
};

struct One {
  int32_t n;
};

struct Two {
  int32_t n;
  int32_t m;
};

class Any {
 public:
  //@ requires 0 <= v.n <= 100
  //@ ensures size() == v.n
  template <typename T>
  explicit Any(T v) : n_(v.n) {}

  //@ ensures result == n_
  int32_t size() const { return n_; }

 private:
  int32_t n_;
};

//@ ensures result == 8
int32_t held() {
  Square s{7};
  const Holder h(std::move(s));
  return h.value();
}

//@ ensures result == 6
int32_t demo() {
  const Any a(One{2});
  const Any b(Two{3, 4});
  return a.size() + b.size();
}
