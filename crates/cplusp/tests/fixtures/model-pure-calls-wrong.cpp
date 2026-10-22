#include <cstdint>
#include <memory>
#include <utility>

// A pure override that reads its field with no null guard, a call on the right of && whose requires line may not hold, and a
// bound that the decorator does not give, decision 0172.
struct Component {
  virtual ~Component() = default;
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
  int32_t cost(int32_t x) const override {
    //@ apply MulBound(x, rate_, 1000, 1000)
    return x * rate_;
  }

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
  //@ ensures 0 <= result <= limit_
  int32_t cost(int32_t x) const override {
    const int32_t inner_cost = inner_->cost(x);
    return inner_cost < limit_ ? inner_cost : limit_;
  }

 private:
  std::unique_ptr<Component> inner_;
  int32_t limit_;
};

class Bare final : public Component {
 public:
  //@ ensures result == (inner_ != nullptr && inner_->valid())
  bool valid() const override { return inner_->valid(); }

  //@ requires valid() && 0 <= x <= 1000
  //@ ensures result == 0
  int32_t cost(int32_t x) const override { return 0; }

  std::unique_ptr<Component> inner_;
};

//@ requires 0 <= x <= 1000
bool cheap(const Component& c, int32_t x) {
  return x > 0 && c.cost(x) < 10;
}

//@ requires 0 <= x <= 1000
//@ ensures 0 <= result <= 299
int32_t quote(int32_t x) {
  std::unique_ptr<Component> base = std::make_unique<Linear>(10);
  std::unique_ptr<Component> mid = std::make_unique<Capped>(std::move(base), 500);
  const Capped outer(std::move(mid), 300);
  return outer.cost(x);
}
