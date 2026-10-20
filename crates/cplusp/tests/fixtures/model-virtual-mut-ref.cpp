#include <cstdint>
#include <memory>

// A virtual function that writes its object and a reference parameter, decision 0169.
class Counter {
 public:
  //@ requires 0 <= start && start <= 1000
  //@ ensures valid() && value() == start
  explicit Counter(int32_t start) : n_(start) {}
  //@ ensures result == (0 <= n_ && n_ <= 1000)
  bool valid() const { return 0 <= n_ && n_ <= 1000; }
  //@ requires valid()
  //@ ensures result == n_
  int32_t value() const { return n_; }
  //@ requires valid() && 0 <= v && v <= 1000
  //@ ensures valid() && value() == v
  void assign(int32_t v) { n_ = v; }

 private:
  int32_t n_;
};

struct Command {
  virtual ~Command() = default;
  virtual bool valid() const = 0;
  virtual bool done() const = 0;
  //@ requires valid() && done()
  //@ ensures 0 <= result && result <= 1000
  virtual int32_t before() const = 0;
  //@ modifies c
  //@ requires valid() && !done() && c.valid() && c.value() < 1000
  //@ ensures valid() && done() && c.valid() && before() == old(c.value()) && c.value() <= old(c.value()) + 1
  virtual void execute(Counter& c) = 0;
};

class Increment final : public Command {
 public:
  //@ ensures valid() && !done()
  Increment() : done_(false), before_(0) {}
  //@ ensures result == (!done_ || (0 <= before_ && before_ <= 1000))
  bool valid() const override { return !done_ || (0 <= before_ && before_ <= 1000); }
  //@ ensures result == done_
  bool done() const override { return done_; }
  //@ requires valid() && done()
  //@ ensures result == before_
  int32_t before() const override { return before_; }
  //@ modifies c
  //@ requires valid() && !done() && c.valid() && c.value() < 1000
  //@ ensures valid() && done() && c.valid() && before() == old(c.value()) && c.value() == old(c.value()) + 1
  void execute(Counter& c) override {
    before_ = c.value();
    c.assign(before_ + 1);
    done_ = true;
  }

 private:
  bool done_;
  int32_t before_;
};

//@ modifies k, c
//@ requires k.valid() && !k.done() && c.valid() && c.value() < 1000
//@ ensures k.valid() && k.done() && c.valid() && k.before() == old(c.value())
void step(Command& k, Counter& c) {
  k.execute(c);
}

//@ ensures result == 5
int32_t demo() {
  Counter c(5);
  std::unique_ptr<Command> k = std::make_unique<Increment>();
  k->execute(c);
  return k->before();
}
