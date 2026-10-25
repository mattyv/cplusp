#include <cstddef>
#include <cstdint>
#include <vector>

// The forms of a vector that have no rule yet, decision 0191.
class Ints {
 public:
  //@ requires values_.size() > 0
  //@ ensures true
  int32_t first() const { return values_.front(); }

  //@ requires values_.size() < 1000
  //@ ensures true
  void grow() { values_.emplace_back(1); }

  // A const reference result that is no field of the object.
  //@ ensures result == a
  const int32_t& pick(const int32_t& a) const { return a; }

 private:
  std::vector<int32_t> values_;
};

// A pop of a local vector.
//@ ensures result == 0
size_t local_pop() {
  std::vector<int32_t> v;
  v.push_back(1);
  v.pop_back();
  return v.size();
}
