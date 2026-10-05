#include <cstdint>
#include <memory>
#include <utility>

// A decorator is a component that owns another component and answers the same interface. This one caps the cost of what it wraps.
// The interface has a contract, and the decorator keeps it for any component inside. The contract of the decorator says how the
// result relates to the result of the inner component, and gives a bound of its own. A caller that holds the decorator by its class
// proves the bound of the decorator, which is stronger than the bound of the interface.
struct Component {
  virtual ~Component() = default;
  // The invariant of each component, decision 0028. The interface cannot know the fields, so it is virtual.
  virtual bool valid() const = 0;
  //@ requires valid() && 0 <= x <= 1000
  //@ ensures 0 <= result <= 1000000
  virtual int32_t cost(int32_t x) const = 0;
};

class Linear final : public Component {
 public:
  //@ requires 0 <= rate <= 1000
  //@ ensures valid() && this->rate_ == rate
  explicit Linear(int32_t rate) : rate_(rate) {}

  //@ ensures result == (0 <= rate_ && rate_ <= 1000)
  bool valid() const override { return 0 <= rate_ && rate_ <= 1000; }

  //@ requires valid() && 0 <= x <= 1000
  //@ ensures result == x * rate_
  int32_t cost(int32_t x) const override { return x * rate_; }

 private:
  int32_t rate_;
};

class Capped final : public Component {
 public:
  //@ requires inner != nullptr && inner->valid() && 0 <= limit <= 1000000
  //@ ensures valid() && this->limit_ == limit
  Capped(std::unique_ptr<Component> inner, int32_t limit) : inner_(std::move(inner)), limit_(limit) {}

  //@ ensures result == (inner_ != nullptr && inner_->valid() && 0 <= limit_ && limit_ <= 1000000)
  bool valid() const override { return inner_ != nullptr && inner_->valid() && 0 <= limit_ && limit_ <= 1000000; }

  //@ requires valid() && 0 <= x <= 1000
  //@ ensures result == (inner_->cost(x) < limit_ ? inner_->cost(x) : limit_)
  //@ ensures 0 <= result <= limit_
  int32_t cost(int32_t x) const override {
    const int32_t inner_cost = inner_->cost(x);
    return inner_cost < limit_ ? inner_cost : limit_;
  }

 private:
  std::unique_ptr<Component> inner_;
  int32_t limit_;
};

// Two decorators over a Linear. The outer one is held by its class, so its own bound of 300 holds. Through the interface, the caller
// would know only the bound of 1000000.
//@ requires 0 <= x <= 1000
//@ ensures 0 <= result <= 300
int32_t quote(int32_t x) {
  std::unique_ptr<Component> base = std::make_unique<Linear>(10);
  std::unique_ptr<Component> mid = std::make_unique<Capped>(std::move(base), 500);
  const Capped outer(std::move(mid), 300);
  return outer.cost(x);
}
