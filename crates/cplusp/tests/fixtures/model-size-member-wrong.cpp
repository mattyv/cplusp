#include <cstddef>
#include <cstdint>
#include <vector>

// Claims through a member function named size or back that do not hold, decision 0200.
class Bag {
 public:
  //@ ensures size() == 0
  Bag() : top_(0) {}

  //@ ensures result == items_.size()
  size_t size() const { return items_.size(); }

  //@ requires size() > 0
  //@ ensures result == items_.back()
  int32_t back() const { return items_.back(); }

  //@ requires size() < 100
  //@ ensures size() == old(size()) && back() == x
  void push(int32_t x) {
    items_.push_back(x);
    top_ = x;
  }

 private:
  std::vector<int32_t> items_;
  int32_t top_;
};

//@ requires b.size() > 0
//@ ensures result == b.back() + 1
int32_t next_of(const Bag& b) {
  return b.back();
}
