#include <cstddef>
#include <cstdint>
#include <vector>

// A class template with type parameters only. Each instantiation is its own type with its own model.
// The capacity is a run-time value, because a non-type template parameter is not in the subset.
// The contracts use the implicit this, decision 0028. Members are in scope by name and are never listed.
// The invariant is the predicate valid(), and every public method requires and ensures it.
template <typename T>
class Stack {
 public:
  //@ requires capacity > 0
  //@ ensures valid() && size() == 0 && this->capacity() == capacity
  explicit Stack(size_t capacity) : capacity_(capacity) {}

  //@ ensures result == (capacity_ > 0 && items_.size() <= capacity_)
  bool valid() const { return capacity_ > 0 && items_.size() <= capacity_; }

  //@ requires valid()
  //@ ensures result == items_.size()
  size_t size() const { return items_.size(); }

  //@ requires valid()
  //@ ensures result == capacity_
  size_t capacity() const { return capacity_; }

  //@ requires valid() && size() < capacity()
  //@ ensures valid() && capacity() == old(capacity()) && size() == old(size()) + 1 && top() == x
  void push(const T& x) { items_.push_back(x); }

  //@ requires valid() && size() > 0
  //@ ensures result == items_[size() - 1]
  const T& top() const { return items_.back(); }

  //@ requires valid() && size() > 0
  //@ ensures valid() && capacity() == old(capacity()) && size() == old(size()) - 1
  void pop() { items_.pop_back(); }

 private:
  std::vector<T> items_;
  size_t capacity_;
};

struct Point {
  int32_t x;
  int32_t y;
};

//@ ensures result == 3
int32_t push_three() {
  Stack<int32_t> s(4);
  s.push(1);
  s.push(2);
  s.push(3);
  return s.top();
}

//@ ensures result == 7
int32_t last_point_y() {
  Stack<Point> s(2);
  s.push(Point{1, 2});
  s.push(Point{5, 7});
  return s.top().y;
}
