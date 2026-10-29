#include <cstddef>
#include <cstdint>
#include <vector>

// A const member function that gives bool has its ensures line as its function, decision 0205.
class Bag {
 public:
  //@ ensures valid() && count() == 0
  Bag() {}

  //@ ensures result == (forall i :: 0 <= i < items_.size() ==> items_[i] >= 0)
  bool valid() const {
    //@ invariant 0 <= i <= items_.size()
    //@ invariant forall j :: 0 <= j < i ==> items_[j] >= 0
    for (size_t i = 0; i < items_.size(); ++i) {
      if (items_[i] < 0) {
        return false;
      }
    }
    return true;
  }

  //@ ensures result == items_.size()
  size_t count() const { return items_.size(); }

  //@ requires valid() && x >= 0 && count() < 100
  //@ ensures valid() && count() == old(count()) + 1
  void push(int32_t x) { items_.push_back(x); }

 private:
  std::vector<int32_t> items_;
};

//@ requires b.valid() && b.count() < 100
//@ modifies b
//@ ensures b.valid() && b.count() == old(b.count()) + 1
void add_two(Bag& b) {
  b.push(2);
}

//@ ensures result
bool fresh() {
  Bag b;
  add_two(b);
  return b.valid();
}
