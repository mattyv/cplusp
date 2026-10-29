#include <cstddef>
#include <cstdint>
#include <vector>

// An integer result and a write keep their rules, decision 0205.
class Bag {
 public:
  //@ ensures result == items_.size()
  size_t total() const {
    size_t n = 0;
    //@ invariant 0 <= i <= items_.size() && n == i
    for (size_t i = 0; i < items_.size(); ++i) {
      n += 1;
    }
    return n;
  }

  //@ requires items_.size() < 100
  //@ ensures result == (items_.size() > 0)
  bool grow() {
    items_.push_back(1);
    return true;
  }

 private:
  std::vector<int32_t> items_;
};

//@ ensures result == b.total()
size_t total_of(const Bag& b) {
  return b.total();
}

//@ modifies b
//@ ensures result == b.grow()
bool grow_of(Bag& b) {
  return b.grow();
}
