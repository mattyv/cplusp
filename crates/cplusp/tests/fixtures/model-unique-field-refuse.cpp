#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

// The forms of a moved unique_ptr that have no rule yet, decision 0171.
struct Component {
  virtual ~Component() = default;
  virtual bool valid() const = 0;
  virtual void bump() = 0;
};

class Unit final : public Component {
 public:
  //@ ensures result == true
  bool valid() const override { return true; }
  void bump() override {}
};

//@ ensures result == true
bool two(std::unique_ptr<Component> p, std::unique_ptr<Component> q) {
  return true;
}

//@ ensures result == true
bool one(std::unique_ptr<Component> p) {
  return true;
}

//@ ensures result == b
bool keep(std::unique_ptr<Component> p, bool b) {
  return b;
}

bool twice() {
  std::unique_ptr<Component> a = std::make_unique<Unit>();
  const bool r = two(std::move(a), std::move(a));
  return r;
}

bool beside() {
  std::unique_ptr<Component> a = std::make_unique<Unit>();
  const bool r = keep(std::move(a), a != nullptr);
  return r;
}

bool param(std::unique_ptr<Component> p) {
  const bool r = one(std::move(p));
  return r;
}

int32_t place() {
  std::unique_ptr<Component> a = std::make_unique<Unit>();
  if (one(std::move(a))) {
    return 1;
  }
  return 0;
}

//@ modifies v
bool element(std::vector<std::unique_ptr<Component>>& v) {
  const bool r = one(std::move(v[0]));
  return r;
}

struct Holder {
  void poke() { inner_->bump(); }

  std::unique_ptr<Component> inner_;
};

class Peek final : public Component {
 public:
  //@ requires 0 <= v && v <= 1000
  //@ ensures valid() && this->v_ == v
  Peek(const std::unique_ptr<Component>& inner, int32_t v) : v_(v) {}
  //@ ensures result == (0 <= v_ && v_ <= 1000)
  bool valid() const override { return 0 <= v_ && v_ <= 1000; }
  void bump() override {}

 private:
  int32_t v_;
};

int32_t peek() {
  std::unique_ptr<Component> base = std::make_unique<Unit>();
  std::unique_ptr<Component> t = std::make_unique<Peek>(std::move(base), 5);
  return 0;
}
