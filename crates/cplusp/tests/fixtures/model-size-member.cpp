#include <cstddef>
#include <cstdint>
#include <vector>

// A member function named size, empty or back, decision 0200.
class Bag {
 public:
  //@ ensures size() == 0 && empty()
  Bag() : top_(0) {}

  //@ ensures result == items_.size()
  size_t size() const { return items_.size(); }

  //@ ensures result == items_.empty()
  bool empty() const { return items_.empty(); }

  //@ requires !empty()
  //@ ensures result == items_.back()
  int32_t back() const { return items_.back(); }

  //@ requires size() < 100
  //@ ensures size() == old(size()) + 1 && back() == x && !empty()
  void push(int32_t x) {
    items_.push_back(x);
    top_ = x;
  }

 private:
  std::vector<int32_t> items_;
  int32_t top_;
};

// A contract calls the members through a parameter.
//@ requires b.size() < 100
//@ modifies b
//@ ensures b.size() == old(b.size()) + 1 && b.back() == 7 && !b.empty()
void add_seven(Bag& b) {
  b.push(7);
}

// A sequence keeps its words.
//@ requires v.size() > 0
//@ ensures result == v.back() && !v.empty()
int32_t last(const std::vector<int32_t>& v) {
  return v.back();
}

//@ ensures result == 7
int32_t seven() {
  Bag b;
  add_seven(b);
  return b.back();
}
