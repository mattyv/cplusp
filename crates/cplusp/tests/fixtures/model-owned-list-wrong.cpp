#include <cstddef>
#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

// A false claim through a field of a vector of unique_ptr of an interface fails, decision 0204.
struct Counter {
  virtual ~Counter() = default;
  virtual int32_t count() const = 0;
  //@ requires count() < 1000
  //@ ensures count() == old(count()) + 1
  virtual void bump() = 0;
};

class One final : public Counter {
 public:
  //@ ensures count() == 0
  One() : n_(0) {}

  //@ ensures result == n_
  int32_t count() const override { return n_; }

  //@ requires count() < 1000
  //@ ensures count() == old(count()) + 1
  void bump() override { n_ += 1; }

 private:
  int32_t n_;
};

class Holder {
 public:
  //@ ensures size() == 0
  Holder() {}

  //@ ensures result == items_.size()
  size_t size() const { return items_.size(); }

  //@ requires i < size() && items_[i] != nullptr
  //@ ensures result == items_[i]->count()
  int32_t count_at(size_t i) const { return items_[i]->count(); }

  //@ requires size() < 100 && o != nullptr
  //@ ensures size() == old(size()) + 1 && items_[old(size())] != nullptr && count_at(old(size())) == old(o->count())
  void add(std::unique_ptr<Counter> o) { items_.push_back(std::move(o)); }

  //@ requires i < size() && items_[i] != nullptr && count_at(i) < 1000
  //@ ensures size() == old(size()) && items_[i] != nullptr && count_at(i) == old(count_at(i)) + 2
  void bump_at(size_t i) { items_[i]->bump(); }

 private:
  std::vector<std::unique_ptr<Counter>> items_;
};

//@ ensures result == 2
int32_t demo() {
  Holder h;
  h.add(std::make_unique<One>());
  h.bump_at(0);
  return h.count_at(0);
}
