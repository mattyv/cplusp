#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

// A vector by value, decision 0194. The callee owns its copy. It adds to the copy, and the caller keeps its own vector.
//@ requires v.size() < 1000
//@ ensures result == v.size() + 1
size_t grown(std::vector<int32_t> v) {
  v.push_back(4);
  return v.size();
}

//@ requires v.size() > 0
//@ ensures result == 1
int32_t first_set(std::vector<int32_t> v) {
  v[0] = 1;
  return v[0];
}

//@ ensures result == v.size()
size_t owned(std::vector<int32_t> v) {
  std::vector<int32_t> w = std::move(v);
  return w.size();
}

class Bag {
 public:
  //@ ensures count() == items.size()
  explicit Bag(std::vector<int32_t> items) : items_(std::move(items)) {}

  //@ ensures result == items_.size()
  size_t count() const { return items_.size(); }

 private:
  std::vector<int32_t> items_;
};

// A copy leaves the source as it was.
//@ ensures result
bool copy_keeps() {
  std::vector<int32_t> a(2, 7);
  size_t n = grown(a);
  return n == 3 && a.size() == 2 && first_set(a) == 1 && a[0] == 7;
}

// A move gives the value to the constructor.
//@ ensures result == 2
size_t moved_in() {
  std::vector<int32_t> a(2, 7);
  const Bag b(std::move(a));
  return b.count();
}
