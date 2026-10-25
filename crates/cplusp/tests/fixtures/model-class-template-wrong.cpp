#include <cstdint>

// A contract of a class template that holds at one type fails at another, decision 0188.
template <typename T>
class Acc {
 public:
  //@ requires 0 <= start && start <= 2000000000
  //@ ensures total() == start
  explicit Acc(T start) : total_(start) {}

  //@ ensures result == total_
  T total() const { return total_; }

  // The sum fits int64_t, but not int32_t.
  //@ requires 0 <= x && x <= 2000000000 && 0 <= total() && total() <= 2000000000
  //@ ensures total() == old(total()) + x
  void add(T x) {
    total_ = total_ + x;
  }

 private:
  T total_;
};

template class Acc<int32_t>;
template class Acc<int64_t>;

// Each instance keeps its own value.
//@ ensures result == 3
int64_t sum() {
  Acc<int64_t> a(1);
  a.add(2);
  a.add(4);
  return a.total();
}
