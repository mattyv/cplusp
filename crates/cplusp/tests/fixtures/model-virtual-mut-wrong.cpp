#include <cstdint>
#include <memory>

// Two overrides that break the contract of a virtual function that writes, and a read of the old value, decision 0169.
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

// Promises less than Observer::on_change.
class Less final : public Observer {
 public:
  //@ ensures result == (0 <= seen_ && seen_ <= 1000)
  bool valid() const override { return 0 <= seen_ && seen_ <= 1000; }
  //@ requires valid()
  //@ ensures result == seen_
  int32_t seen() const override { return seen_; }
  //@ requires valid() && seen() < 1000
  //@ ensures valid()
  void on_change(int32_t) override { seen_ += 1; }

 private:
  int32_t seen_;
};

// Requires more than Observer::on_change.
class More final : public Observer {
 public:
  //@ ensures valid() && seen() == 0
  More() : seen_(0) {}
  //@ ensures result == (0 <= seen_ && seen_ <= 1000)
  bool valid() const override { return 0 <= seen_ && seen_ <= 1000; }
  //@ requires valid()
  //@ ensures result == seen_
  int32_t seen() const override { return seen_; }
  //@ requires valid() && seen() < 500
  //@ ensures valid() && seen() == old(seen()) + 1
  void on_change(int32_t) override { seen_ += 1; }

 private:
  int32_t seen_;
};

// The object after the call is no longer the object before it.
//@ ensures result == 1
int32_t stale() {
  std::unique_ptr<Observer> p = std::make_unique<More>();
  p->on_change(3);
  //@ assert p->seen() == 0
  return p->seen();
}
