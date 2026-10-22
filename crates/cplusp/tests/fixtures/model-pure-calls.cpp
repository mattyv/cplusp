#include <cstdint>
#include <memory>
#include <utility>

// Pure overrides that call the interface through a field, with a local before the return, and a call of a virtual function on
// the right of &&, decision 0172. Capped and quote are the example decorator.
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

class Pass final : public Component {
 public:
  //@ requires inner != nullptr && inner->valid()
  //@ ensures valid()
  explicit Pass(std::unique_ptr<Component> inner) : inner_(std::move(inner)) {}

  //@ ensures result == (inner_ != nullptr && inner_->valid())
  bool valid() const override { return inner_ != nullptr && inner_->valid(); }

  //@ requires valid() && 0 <= x <= 1000
  //@ ensures result == inner_->cost(x)
  int32_t cost(int32_t x) const override { return inner_->cost(x); }

 private:
  std::unique_ptr<Component> inner_;
};

//@ requires 0 <= x <= 1000
//@ ensures 0 <= result <= 300
int32_t quote(int32_t x) {
  std::unique_ptr<Component> base = std::make_unique<Linear>(10);
  std::unique_ptr<Component> mid = std::make_unique<Capped>(std::move(base), 500);
  const Capped outer(std::move(mid), 300);
  return outer.cost(x);
}

//@ requires 0 <= x <= 1000
//@ ensures 0 <= result <= 1000000
int32_t through(int32_t x) {
  std::unique_ptr<Component> lin = std::make_unique<Linear>(4);
  std::unique_ptr<Component> p = std::make_unique<Pass>(std::move(lin));
  return p->cost(x);
}

//@ requires c.valid() && 0 <= x <= 1000
//@ ensures result == (x > 0 && c.cost(x) < 10)
bool cheap(const Component& c, int32_t x) {
  return x > 0 && c.cost(x) < 10;
}

//@ requires c.valid() && 0 <= x <= 1000
//@ ensures 0 <= result && result <= 3
int32_t steps(const Component& c, int32_t x) {
  int32_t n = 0;
  //@ invariant 0 <= n && n <= 3
  //@ decreases 3 - n
  while (n < 3 && c.cost(x) >= 0) {
    ++n;
  }
  return n;
}
