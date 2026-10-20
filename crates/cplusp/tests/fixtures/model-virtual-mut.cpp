#include <cstdint>
#include <memory>

// A virtual function that writes its object, through a reference of the interface and through a unique_ptr, decision 0169.
struct Observer {
  virtual ~Observer() = default;
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures 0 <= result && result <= 1000
  virtual int32_t seen() const = 0;
  //@ requires valid() && seen() < 1000
  //@ ensures valid() && seen() == old(seen()) + 1
  virtual void on_change(int32_t v) = 0;
};

class Tally final : public Observer {
 public:
  //@ ensures valid() && seen() == 0
  Tally() : seen_(0) {}
  //@ ensures result == (0 <= seen_ && seen_ <= 1000)
  bool valid() const override { return 0 <= seen_ && seen_ <= 1000; }
  //@ requires valid()
  //@ ensures result == seen_
  int32_t seen() const override { return seen_; }
  //@ requires valid() && seen() < 1000
  //@ ensures valid() && seen() == old(seen()) + 1
  void on_change(int32_t) override { seen_ += 1; }

 private:
  int32_t seen_;
};

//@ modifies o
//@ requires o.valid() && o.seen() < 999
//@ ensures o.valid() && o.seen() == old(o.seen()) + 2
void ping(Observer& o) {
  o.on_change(1);
  o.on_change(2);
}

//@ ensures result == 1
int32_t once() {
  std::unique_ptr<Observer> p = std::make_unique<Tally>();
  p->on_change(3);
  return p->seen();
}
