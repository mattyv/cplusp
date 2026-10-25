#include <cstdint>

// Static polymorphism. The classic form is the curiously recurring template pattern: `template <class Derived> struct Base`, whose
// member function calls the hook of the class that derives from it, `static_cast<const Derived&>(*this).step()`, and `struct Impl :
// Base<Impl>`. The gate takes it: "ok: no findings". The downcast rows say nothing about a downcast inside a template, and the same
// holds for a function template that casts a polymorphic base to a derived class. Probably the check skips template instantiations.
// This folder does not keep it. A downcast is what the row bans, and the model has no way to say that a Base<Impl> is
// only ever the base of an Impl. The shape the subset takes is a template that holds the implementation as a member of its type
// parameter and calls it. There is no base class and no cast. The algorithm sits in the template and the hook in the parameter.
struct Negate {
  //@ ensures result == true
  bool valid() const { return true; }

  //@ requires valid() && -1000000 <= x <= 1000000
  //@ ensures result == -x && -1000000 <= result <= 1000000
  int32_t apply(int32_t x) const { return -x; }
};

class Cap {
 public:
  //@ requires -1000000 <= limit <= 1000000
  //@ ensures valid() && this->limit_ == limit
  explicit Cap(int32_t limit) : limit_(limit) {}

  //@ ensures result == (-1000000 <= limit_ && limit_ <= 1000000)
  bool valid() const { return -1000000 <= limit_ && limit_ <= 1000000; }

  //@ requires valid() && -1000000 <= x <= 1000000
  //@ ensures result == (x < limit_ ? x : limit_) && -1000000 <= result <= 1000000
  int32_t apply(int32_t x) const { return x < limit_ ? x : limit_; }

 private:
  int32_t limit_;
};

// The template is verified once for each Step it is used at. It runs the step twice.
template <typename Step>
class Twice {
 public:
  //@ requires step.valid()
  //@ ensures valid() && this->step_ == step
  explicit Twice(Step step) : step_(step) {}

  //@ ensures result == step_.valid()
  bool valid() const { return step_.valid(); }

  //@ requires valid() && -1000000 <= x <= 1000000
  //@ ensures result == step_.apply(step_.apply(x)) && -1000000 <= result <= 1000000
  int32_t run(int32_t x) const { return step_.apply(step_.apply(x)); }

 private:
  Step step_;
};

// An explicit instantiation makes the body of each member function of an instance, decision 0188.
template class Twice<Negate>;
template class Twice<Cap>;

// Negating twice gives the number back.
//@ requires -1000000 <= x <= 1000000
//@ ensures result == x
int32_t negate_twice(int32_t x) {
  const Twice<Negate> t{Negate{}};
  return t.run(x);
}

// Capping twice is capping once.
//@ requires -1000000 <= x <= 1000000
//@ ensures result == (x < 5 ? x : 5)
int32_t cap_twice(int32_t x) {
  const Twice<Cap> t{Cap(5)};
  return t.run(x);
}
