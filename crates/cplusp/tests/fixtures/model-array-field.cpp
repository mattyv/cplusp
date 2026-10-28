#include <array>
#include <cstddef>
#include <cstdint>

// A class that holds a std::array, decision 0196.
class Slots {
 public:
  //@ ensures size() == 8 && forall i :: 0 <= i < 8 ==> items_[i] == 0
  Slots() : items_() {}

  //@ ensures result == items_.size()
  size_t size() const { return items_.size(); }

  //@ requires i < 8
  //@ ensures result == items_[i]
  int32_t at(size_t i) const { return items_.at(i); }

  //@ requires i < 8
  //@ ensures items_[i] == x
  //@ ensures forall k :: 0 <= k < 8 && k != i ==> items_[k] == old(items_[k])
  void put(size_t i, int32_t x) { items_[i] = x; }

 private:
  std::array<int32_t, 8> items_;
};

// A default member initializer gives the zeros too. The length holds in an object that a caller gives.
class Pair {
 public:
  //@ ensures first() == a && second() == 0
  explicit Pair(int32_t a) : w_(a) {}

  //@ ensures result == w_
  int32_t first() const { return w_; }

  //@ ensures result == 2
  size_t length() const { return v_.size(); }

  //@ ensures result == v_[1]
  int32_t second() const { return v_[1]; }

 private:
  std::array<int32_t, 2> v_{};
  int32_t w_;
};

//@ ensures result == 2
size_t length_of(const Pair& p) {
  return p.length();
}

//@ ensures result == 5
int32_t caller() {
  Slots s;
  s.put(3, 5);
  s.put(4, 9);
  return s.at(3);
}

//@ ensures result == 0
int32_t zero_start() {
  Slots s;
  const Pair p(4);
  return s.at(7) + p.second();
}
