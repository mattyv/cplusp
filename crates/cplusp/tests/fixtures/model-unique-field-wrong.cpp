#include <cstdint>
#include <memory>
#include <utility>

// A field read through a unique_ptr keeps the null check and the contract of the interface, and a moved value meets the requires
// lines of the callee, decision 0171.
struct Component {
  virtual ~Component() = default;
  virtual bool valid() const = 0;
  //@ requires valid() && 0 <= x && x <= 1000
  //@ ensures 0 <= result && result <= 1000000
  virtual int32_t cost(int32_t x) const = 0;
};

struct Holder {
  //@ requires inner != nullptr && inner->valid()
  //@ ensures this->inner_ != nullptr && this->inner_->valid()
  explicit Holder(std::unique_ptr<Component> inner) : inner_(std::move(inner)) {}

  //@ requires (inner_ == nullptr || inner_->valid()) && 0 <= x && x <= 1000
  //@ ensures 0 <= result && result <= 1000000
  int32_t unguarded(int32_t x) const { return inner_->cost(x); }

  //@ requires inner_ != nullptr && 0 <= x && x <= 1000
  //@ ensures 0 <= result && result <= 1000000
  int32_t unchecked(int32_t x) const { return inner_->cost(x); }

  std::unique_ptr<Component> inner_;
};

class Unit final : public Component {
 public:
  //@ ensures result == true
  bool valid() const override { return true; }
  //@ requires valid() && 0 <= x && x <= 1000
  //@ ensures result == 0
  int32_t cost(int32_t x) const override { return 0; }
};

//@ ensures result != nullptr
std::unique_ptr<Component> any() {
  return std::make_unique<Unit>();
}

int32_t hold() {
  std::unique_ptr<Component> a = any();
  const Holder h(std::move(a));
  return 0;
}
