#include <cstddef>
#include <cstdint>
#include <memory>
#include <vector>

// A vector of unique_ptr of an interface whose elements a call writes, and a local vector passed by reference, decision 0170.
class Counter {
 public:
  //@ requires 0 <= start <= 1000
  //@ ensures valid() && value() == start
  explicit Counter(int32_t start) : n_(start) {}

  //@ ensures result == (0 <= n_ && n_ <= 1000)
  bool valid() const { return 0 <= n_ && n_ <= 1000; }

  //@ requires valid()
  //@ ensures result == n_
  int32_t value() const { return n_; }

  //@ requires valid() && 0 <= v <= 1000
  //@ ensures valid() && value() == v
  void assign(int32_t v) { n_ = v; }

 private:
  int32_t n_;
};

struct Command {
  virtual ~Command() = default;
  // The invariant of each command, decision 0028. The interface cannot know the fields, so it is virtual.
  virtual bool valid() const = 0;
  // Whether the command has run and not been taken back.
  virtual bool done() const = 0;
  // The counter value at the time the command ran.
  //@ requires valid() && done()
  //@ ensures 0 <= result <= 1000
  virtual int32_t before() const = 0;
  // A command raises the counter by one at most. That is what lets the driver keep every step in range.
  //@ modifies c
  //@ requires valid() && !done() && c.valid() && c.value() < 1000
  //@ ensures valid() && done() && c.valid() && before() == old(c.value()) && c.value() <= old(c.value()) + 1
  virtual void execute(Counter& c) = 0;
  //@ modifies c
  //@ requires valid() && done() && c.valid()
  //@ ensures valid() && !done() && c.valid() && c.value() == old(before())
  virtual void undo(Counter& c) = 0;
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

  //@ modifies c
  //@ requires valid() && done() && c.valid()
  //@ ensures valid() && !done() && c.valid() && c.value() == old(before())
  void undo(Counter& c) override {
    c.assign(before_);
    done_ = false;
  }

 private:
  bool done_;
  int32_t before_;
};

// The driver. The commands are owned by the vector, and running one changes it, so the vector is a non-const parameter.
//@ requires cmds.size() <= 100
//@ requires forall j :: 0 <= j < cmds.size() ==> cmds[j] != nullptr
//@ requires forall j :: 0 <= j < cmds.size() ==> cmds[j]->valid() && !cmds[j]->done()
//@ requires c.valid() && c.value() <= 900
//@ ensures c.valid() && c.value() == old(c.value())
//@ ensures forall j :: 0 <= j < cmds.size() ==> cmds[j] != nullptr && cmds[j]->valid() && !cmds[j]->done()
void run_and_undo(std::vector<std::unique_ptr<Command>>& cmds, Counter& c) {
  const size_t n = cmds.size();
  //@ invariant 0 <= i <= n && n == cmds.size()
  //@ invariant c.valid() && c.value() <= old(c.value()) + i
  //@ invariant i == 0 ==> c.value() == old(c.value())
  //@ invariant forall j :: 0 <= j < n ==> cmds[j] != nullptr
  //@ invariant forall j :: 0 <= j < i ==> cmds[j]->valid() && cmds[j]->done()
  //@ invariant forall j :: i <= j < n ==> cmds[j]->valid() && !cmds[j]->done()
  //@ invariant i > 0 ==> cmds[0]->before() == old(c.value())
  for (size_t i = 0; i < n; ++i) {
    cmds[i]->execute(c);
  }
  //@ invariant 0 <= i <= n && n == cmds.size() && c.valid()
  //@ invariant forall j :: 0 <= j < n ==> cmds[j] != nullptr
  //@ invariant forall j :: 0 <= j < i ==> cmds[j]->valid() && cmds[j]->done()
  //@ invariant forall j :: i <= j < n ==> cmds[j]->valid() && !cmds[j]->done()
  //@ invariant i > 0 ==> cmds[0]->before() == old(c.value())
  //@ invariant i == 0 ==> c.value() == old(c.value())
  for (size_t i = n; i > 0; --i) {
    cmds[i - 1]->undo(c);
  }
}

// A call through an element of a local vector writes the element back.
//@ ensures result == 6
int32_t one_step() {
  Counter c(5);
  std::vector<std::unique_ptr<Command>> cmds;
  cmds.push_back(std::make_unique<Increment>());
  cmds[0]->execute(c);
  return c.value();
}

// Two commands from 5. The counter is 6, then 7, and then it is taken back to 5.
//@ ensures result == 5
int32_t demo() {
  Counter c(5);
  std::vector<std::unique_ptr<Command>> cmds;
  cmds.push_back(std::make_unique<Increment>());
  cmds.push_back(std::make_unique<Increment>());
  run_and_undo(cmds, c);
  return c.value();
}
