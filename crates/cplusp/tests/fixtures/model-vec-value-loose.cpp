#include <cstddef>
#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

// A team that loosens rvalue_references reads a vector after it gives it to a parameter by value. The model keeps no value for
// it, decision 0194.
class Bag {
 public:
  //@ ensures count() == items.size()
  explicit Bag(std::vector<int32_t> items) : items_(std::move(items)) {}

  //@ ensures result == items_.size()
  size_t count() const { return items_.size(); }

 private:
  std::vector<int32_t> items_;
};

//@ ensures result
bool after_move() {
  std::vector<int32_t> a(2, 7);
  const Bag b(std::move(a));
  return a.empty() && b.count() == 2;
}

void sink(std::vector<int32_t> v) { v.push_back(1); }

// A call that stands alone gives the vector up too.
//@ ensures result
bool after_sink() {
  std::vector<int32_t> a(2, 7);
  sink(std::move(a));
  return !a.empty();
}

struct Cell {
  int32_t value = 7;
};

//@ ensures result == v.size()
size_t mix(std::unique_ptr<Cell> p, std::vector<int32_t> v) { return v.size(); }

// One call moves a unique_ptr and a vector. The unique_ptr is null after it.
//@ ensures result
bool mixed() {
  std::vector<int32_t> a(2, 7);
  std::unique_ptr<Cell> p = std::make_unique<Cell>();
  size_t n = mix(std::move(p), std::move(a));
  return p == nullptr && n == 2;
}
