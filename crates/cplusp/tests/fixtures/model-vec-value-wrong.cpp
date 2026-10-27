#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

// Claims about a vector by value that do not hold, decision 0194.
//@ requires v.size() < 1000
//@ ensures result == v.size()
size_t grown(std::vector<int32_t> v) {
  v.push_back(4);
  return v.size();
}

class Bag {
 public:
  //@ ensures count() == items.size() + 1
  explicit Bag(std::vector<int32_t> items) : items_(std::move(items)) {}

  //@ ensures result == items_.size()
  size_t count() const { return items_.size(); }

 private:
  std::vector<int32_t> items_;
};

// The write of the callee is not a write of the caller.
//@ ensures result == 3
size_t leaks() {
  std::vector<int32_t> a(2, 7);
  size_t n = grown(a);
  return a.size() + n - n;
}
