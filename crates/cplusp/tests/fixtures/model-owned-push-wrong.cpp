#include <cstddef>
#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

// A push of std::move(o) leaves o null, in a field, a vector by reference and a local vector, decision 0204. A claim that the second element is not null fails.
struct Counter {
  virtual ~Counter() = default;
  virtual int32_t count() const = 0;
};

class Holder {
 public:
  //@ ensures result == items_.size()
  size_t size() const { return items_.size(); }

  //@ requires size() < 100 && o != nullptr
  //@ ensures size() == old(size()) + 2 && items_[old(size())] != nullptr && items_[old(size()) + 1] != nullptr
  void add_twice(std::unique_ptr<Counter> o) {
    items_.push_back(std::move(o));
    items_.push_back(std::move(o));
  }

 private:
  std::vector<std::unique_ptr<Counter>> items_;
};

//@ requires v.size() < 100 && o != nullptr
//@ modifies v
//@ ensures v.size() == old(v.size()) + 2 && v[old(v.size())] != nullptr && v[old(v.size()) + 1] != nullptr
void h(std::vector<std::unique_ptr<Counter>>& v, std::unique_ptr<Counter> o) {
  v.push_back(std::move(o));
  v.push_back(std::move(o));
}

//@ requires o != nullptr
//@ ensures result
bool k(std::unique_ptr<Counter> o) {
  std::vector<std::unique_ptr<Counter>> v;
  v.push_back(std::move(o));
  v.push_back(std::move(o));
  return v.size() == 2 && v[0] != nullptr && v[1] != nullptr;
}
