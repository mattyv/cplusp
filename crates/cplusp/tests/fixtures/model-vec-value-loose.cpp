#include <cstddef>
#include <cstdint>
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
