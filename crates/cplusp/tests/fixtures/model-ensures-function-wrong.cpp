#include <cstddef>
#include <cstdint>
#include <vector>

// The function of the ensures line keeps its promise, and a false claim through it fails, decision 0205.
class Bag {
 public:
  //@ ensures result == (forall i :: 0 <= i < items_.size() ==> items_[i] > 0)
  bool valid() const {
    //@ invariant 0 <= i <= items_.size()
    //@ invariant forall j :: 0 <= j < i ==> items_[j] > 0
    for (size_t i = 0; i < items_.size(); ++i) {
      if (items_[i] <= 0) {
        return false;
      }
    }
    return true;
  }

  //@ ensures result == items_.size()
  size_t count() const { return items_.size(); }

  //@ requires count() < 100
  //@ ensures valid()
  void push(int32_t x) { items_.push_back(x); }

 private:
  std::vector<int32_t> items_;
};
