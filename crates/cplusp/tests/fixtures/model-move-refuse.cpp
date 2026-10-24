#include <cstdint>
#include <utility>

// A constructor body that reads or writes a field, or uses `this`, a `T&&` parameter of a scalar, and a move constructor in a
// struct with no destructor, decision 0179.
class Box {
 public:
  //@ ensures value() == 1
  Box() : value_(0) { value_ = 1; }

  //@ ensures value() == v
  explicit Box(int32_t v) : value_(v) {
    int32_t w = value_;
  }

  //@ modifies other
  //@ ensures true
  Box(Box&& other) noexcept : value_(other.value_) { this->value_ = 2; }

  //@ ensures true
  ~Box() {}

  //@ ensures result == value_
  int32_t value() const { return value_; }

 private:
  int32_t value_;
};

//@ ensures result == x
int32_t keep(int32_t&& x) {
  return x;
}

class Bare {
 public:
  //@ ensures true
  Bare() : n_(0) {}

  //@ modifies other
  //@ ensures true
  Bare(Bare&& other) noexcept : n_(other.n_) {}

 private:
  int32_t n_;
};

// A destructor `= default` is no destructor of the model, so the move constructor has no rule.
class Soft {
 public:
  //@ ensures true
  Soft() : n_(0) {}

  //@ modifies other
  //@ ensures true
  Soft(Soft&& other) noexcept : n_(0) {}

  ~Soft() = default;

 private:
  int32_t n_;
};

// A move constructor that the file only declares. The return of a local can run it or skip it.
class Far {
 public:
  //@ ensures value() == v
  explicit Far(int32_t v) : value_(v) {}

  Far(Far&& other) noexcept;

  //@ ensures result == value_
  int32_t value() const { return value_; }

 private:
  int32_t value_;
};

//@ ensures result.value() == 5
Far far() {
  Far f(5);
  return f;
}

// A copy constructor that the file only declares. The return of a local can run it or skip it.
class Kept {
 public:
  //@ ensures value() == v
  explicit Kept(int32_t v) : value_(v) {}

  Kept(const Kept& other);

  //@ ensures result == value_
  int32_t value() const { return value_; }

 private:
  int32_t value_;
};

//@ ensures result.value() == 5
Kept kept() {
  Kept k(5);
  return k;
}
