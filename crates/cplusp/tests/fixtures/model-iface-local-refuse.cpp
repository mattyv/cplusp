#include <cstdint>

// A local of a final class through a reference to its interface, decision 0208. A field and a parameter of the class have no rule yet.

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

//@ requires s.valid() && s.seen() <= 1000
//@ modifies s
//@ ensures s.valid() && s.seen() == old(s.seen()) + 3
void add_three(Sink& s) {
  s.add(3);
}

struct Holder {
  Total t;
  //@ requires t.valid() && t.seen() <= 1000
  //@ ensures true
  void bump() { add_three(t); }
};

//@ requires t.valid() && t.seen() <= 1000
//@ modifies t
//@ ensures true
void pass_param(Total& t) {
  add_three(t);
}
