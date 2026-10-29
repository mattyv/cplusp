#include <cstdint>

// A write-back through an interface with no final class is refused in each place of a body, decision 0217.

struct Sink {
  virtual ~Sink() = default;
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures result >= 0
  virtual int64_t seen() const = 0;
  //@ requires valid() && seen() <= 1000 && 0 <= k <= 10
  //@ ensures valid() && seen() == old(seen()) + k
  virtual void add(int32_t k) = 0;
};

class Total final : public Sink {
 public:
  //@ ensures valid() && seen() == 0
  Total() : total_(0) {}
  //@ ensures result == (0 <= total_ && total_ <= 2000)
  bool valid() const override { return 0 <= total_ && total_ <= 2000; }
  //@ requires valid()
  //@ ensures result == total_
  int64_t seen() const override { return total_; }
  //@ requires valid() && seen() <= 1000 && 0 <= k <= 10
  //@ ensures valid() && seen() == old(seen()) + k
  void add(int32_t k) override { total_ += k; }
 private:
  int64_t total_;
};
struct Poker {
  virtual ~Poker() = default;
  //@ requires s.valid()
  //@ modifies s
  //@ ensures s.valid() && s.seen() == 5000
  virtual void poke(Sink& s) const = 0;
};

enum class Mode { A, B };

//@ requires s.valid() && s.seen() <= 1000
//@ modifies s
//@ ensures s.valid() && s.seen() == old(s.seen()) + 3 && result == 0
int64_t add_ret(Sink& s) {
  s.add(3);
  return 0;
}

//@ requires s.valid() && s.seen() <= 1000
//@ modifies s
//@ ensures s.valid() && s.seen() == old(s.seen()) + 3
void add_three(Sink& s) {
  s.add(3);
}

//@ ensures result == 42
int64_t w_if(bool b) {
  Total t;
  if (b) {
    int64_t k = 0;
  } else {
    add_three(t);
  }
  return t.seen();
}

//@ ensures result == 42
int64_t w_while() {
  Total t;
  int32_t i = 0;
  //@ invariant 0 <= i <= 1
  //@ decreases 1 - i
  while (i < 1) {
    { add_three(t); }
    i = i + 1;
  }
  return 0;
}

//@ ensures result == 42
int64_t w_for() {
  Total t;
  //@ invariant 0 <= i <= 1
  //@ decreases 1 - i
  for (int32_t i = 0; i < 1; i = i + 1) {
    add_three(t);
  }
  return 0;
}

//@ ensures result == 42
int64_t w_switch(Mode m) {
  Total t;
  switch (m) {
    case Mode::A:
      add_three(t);
      break;
    case Mode::B:
      break;
  }
  return 0;
}

//@ ensures result == 42
int64_t w_local() {
  Total t;
  int64_t r = add_ret(t);
  return r;
}

//@ ensures result == 42
int64_t w_return() {
  Total t;
  return add_ret(t);
}

//@ ensures result == 42
int64_t w_assign() {
  Total t;
  int64_t r = 1;
  r = add_ret(t);
  return r;
}

//@ ensures result == 42
int64_t w_pre() {
  Total t;
  int64_t r = add_ret(t) + 1;
  return r;
}
