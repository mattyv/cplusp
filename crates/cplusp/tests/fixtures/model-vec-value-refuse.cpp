#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

// The forms of a vector by value that have no rule, decision 0194.
class Probe {
 public:
  //@ ensures result == v.size()
  size_t any(std::vector<int32_t> v) const { return v.size(); }

  //@ requires any(v) > 0
  //@ ensures true
  int32_t first(std::vector<int32_t> v) const { return v.at(0); }
};

//@ ensures true
size_t flags(std::vector<bool> v) {
  return v.size();
}

//@ ensures true
size_t take(std::vector<int32_t> v) {
  return v.size();
}

// A move of a vector inside an expression, and into a call that starts a local vector.
//@ ensures true
bool in_test() {
  std::vector<int32_t> a(2, 7);
  if (take(std::move(a)) == 2) {
    return true;
  }
  return false;
}

//@ ensures true
size_t in_sum() {
  std::vector<int32_t> a(2, 7);
  size_t n = take(std::move(a)) + 0;
  return n;
}

//@ requires v.size() < 1000
//@ ensures true
std::vector<int32_t> pushed(std::vector<int32_t> v) {
  v.push_back(1);
  return v;
}

//@ ensures true
size_t into_vector() {
  std::vector<int32_t> a(2, 7);
  std::vector<int32_t> b = pushed(std::move(a));
  return b.size();
}

struct Holder {
  std::vector<int32_t> xs;
};

//@ ensures true
size_t holders(std::vector<Holder> v) {
  return v.size();
}
