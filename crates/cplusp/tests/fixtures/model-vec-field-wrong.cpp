#include <cstddef>
#include <cstdint>
#include <vector>

// Claims about a vector field that do not hold, decision 0191.
class Ints {
 public:
  //@ ensures result == values_.size()
  size_t size() const { return values_.size(); }

  //@ requires size() < 1000
  //@ ensures size() == old(size()) + 1
  void push(int32_t x) { values_.push_back(x); }

  // A pop of an empty vector is undefined behaviour.
  //@ ensures size() == old(size()) - 1
  void drop() { values_.pop_back(); }

  // So is the last element of an empty vector.
  //@ ensures true
  int32_t peek() const { return values_.back(); }

 private:
  std::vector<int32_t> values_;
};

// A pop takes the last element away, so the one before is last.
//@ requires i.size() == 0
//@ modifies i
//@ ensures result == 7
int32_t after(Ints& i) {
  i.push(1);
  i.push(7);
  i.drop();
  return i.peek();
}
