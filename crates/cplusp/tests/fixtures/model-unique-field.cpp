#include <cstdint>
#include <memory>
#include <utility>

// A unique_ptr of an interface as a field and as a parameter by value, and std::move of a local into it, decision 0171.
struct Component {
  virtual ~Component() = default;
  virtual bool valid() const = 0;
  //@ requires valid() && 0 <= x && x <= 1000
  //@ ensures 0 <= result && result <= 1000000
  virtual int32_t cost(int32_t x) const = 0;
};

class Linear final : public Component {
 public:
  //@ requires 0 <= rate && rate <= 1000
  //@ ensures valid() && this->rate_ == rate
  explicit Linear(int32_t rate) : rate_(rate) {}
  //@ ensures result == (0 <= rate_ && rate_ <= 1000)
  bool valid() const override { return 0 <= rate_ && rate_ <= 1000; }
  //@ requires valid() && 0 <= x && x <= 1000
  //@ ensures result == x * rate_
  int32_t cost(int32_t x) const override {
    //@ apply MulBound(x, rate_, 1000, 1000)
    return x * rate_;
  }

 private:
  int32_t rate_;
};

struct Holder {
  //@ requires inner != nullptr && inner->valid() && 0 <= limit && limit <= 1000000
  //@ ensures this->inner_ != nullptr && this->inner_->valid() && this->limit_ == limit
  Holder(std::unique_ptr<Component> inner, int32_t limit) : inner_(std::move(inner)), limit_(limit) {}

  //@ requires inner_ != nullptr && inner_->valid() && 0 <= x && x <= 1000
  //@ ensures 0 <= result && result <= 1000000
  int32_t inner_cost(int32_t x) const { return inner_->cost(x); }

  std::unique_ptr<Component> inner_;
  int32_t limit_;
};

//@ requires p != nullptr && p->valid() && 0 <= x && x <= 1000
//@ ensures 0 <= result && result <= 1000000
int32_t run(std::unique_ptr<Component> p, int32_t x) {
  return p->cost(x);
}

//@ requires 0 <= x && x <= 1000
//@ ensures 0 <= result && result <= 1000000
int32_t demo(int32_t x) {
  std::unique_ptr<Component> base = std::make_unique<Linear>(10);
  const Holder h(std::move(base), 500);
  return h.inner_cost(x);
}

//@ requires 0 <= x && x <= 1000
//@ ensures 0 <= result && result <= 1000000
int32_t direct(int32_t x) {
  const Holder h(std::make_unique<Linear>(10), 500);
  return h.inner_cost(x);
}

//@ requires 0 <= x && x <= 1000
//@ ensures 0 <= result && result <= 1000000
int32_t moved(int32_t x) {
  std::unique_ptr<Component> a = std::make_unique<Linear>(7);
  std::unique_ptr<Component> b = std::move(a);
  const int32_t r = run(std::move(b), x);
  return r;
}

//@ ensures result != nullptr && result->valid()
std::unique_ptr<Component> pass() {
  std::unique_ptr<Component> a = std::make_unique<Linear>(3);
  return std::move(a);
}

//@ ensures result == 0
int32_t after() {
  std::unique_ptr<Component> a = std::make_unique<Linear>(1);
  const int32_t r = run(std::move(a), 1);
  return a != nullptr ? r : 0;
}

class Tag final : public Component {
 public:
  //@ requires inner != nullptr && inner->valid() && 0 <= v && v <= 1000
  //@ ensures valid() && this->v_ == v
  Tag(std::unique_ptr<Component> inner, int32_t v) : inner_(std::move(inner)), v_(v) {}
  //@ ensures result == (0 <= v_ && v_ <= 1000)
  bool valid() const override { return 0 <= v_ && v_ <= 1000; }
  //@ requires valid() && 0 <= x && x <= 1000
  //@ ensures result == v_
  int32_t cost(int32_t x) const override { return v_; }

 private:
  std::unique_ptr<Component> inner_;
  int32_t v_;
};

//@ requires 0 <= x && x <= 1000
//@ ensures result == 5
int32_t nested(int32_t x) {
  std::unique_ptr<Component> base = std::make_unique<Linear>(10);
  std::unique_ptr<Component> t = std::make_unique<Tag>(std::move(base), 5);
  return t->cost(x);
}
