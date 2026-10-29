#include <cstdint>
#include <memory>

// Calls that keep the rules of 0104 and 0172, decision 0189.

// A member function whose body holds a call is no plain member function.
struct Deep {
  //@ ensures result == 1
  int32_t one() const { return 1; }

  //@ ensures result == 1
  int32_t again() const { return one(); }
};

struct Top {
  Deep d;

  //@ ensures result == 1
  int32_t top() const { return d.again(); }
};

//@ requires t.top() == 1
//@ ensures result == 1
int32_t use_top(const Top& t) {
  return 1;
}

// A plain member function whose contract has no model stays a method.
struct Odd {
  int32_t v = 0;

  //@ ensures result == v &&& 1
  int32_t get() const { return v; }
};

//@ ensures result == o.v
int32_t use_odd(const Odd& o) {
  return o.get() + 0;
}

// A member function that calls a plain member function whose contract has no model is no pure function.
struct Odd2 {
  int32_t v = 0;

  //@ ensures result == v &&& 1
  int32_t get() const { return v; }

  //@ ensures result == v
  int32_t g2() const { return get(); }
};

//@ requires o.g2() == 0
//@ ensures true
int32_t use_g2(const Odd2& o) {
  return o.v;
}

// A call of a const virtual function of an interface is no call of a plain member function.
struct Part {
  virtual ~Part() = default;
  virtual bool valid() const = 0;
};

class Whole final : public Part {
 public:
  //@ ensures result == (inner_ != nullptr && inner_->valid())
  bool valid() const override { return inner_ != nullptr && inner_->valid(); }

  //@ ensures result == (valid() ? 1 : 0)
  int32_t outer() const { return valid() ? 1 : 0; }

 private:
  std::unique_ptr<Part> inner_;
};

//@ requires w.outer() == 1
//@ ensures true
int32_t use_outer(const Whole& w) {
  return 0;
}

// A requires line that calls a member function that calls back is a cycle, and Dafny cannot prove that it ends, decision 0190.
struct Loopy {
  int32_t v = 0;

  //@ requires ok()
  //@ ensures result == v
  int32_t get() const { return v; }

  //@ ensures result == (v == 0)
  bool ok() const { return v == 0 && get() == 0; }
};
