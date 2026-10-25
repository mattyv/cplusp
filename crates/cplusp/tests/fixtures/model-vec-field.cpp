#include <cstddef>
#include <cstdint>
#include <vector>

// A vector field that grows and shrinks, decision 0191.
struct Point {
  int32_t x = 0;
  int32_t y = 0;
};

class Points {
 public:
  //@ requires capacity > 0
  //@ ensures size() == 0 && this->capacity() == capacity
  explicit Points(size_t capacity) : capacity_(capacity) {}

  //@ ensures result == items_.size()
  size_t size() const { return items_.size(); }

  // A const reference to a field is its value.
  //@ ensures result == capacity_
  const size_t& capacity() const { return capacity_; }

  //@ requires size() < capacity()
  //@ ensures size() == old(size()) + 1 && capacity() == old(capacity()) && top() == p
  //@ ensures forall i :: 0 <= i < old(size()) ==> at(i) == old(at(i))
  void push(const Point& p) { items_.push_back(p); }

  // A const reference to the last element is its value.
  //@ requires size() > 0
  //@ ensures result == items_.back()
  const Point& top() const { return items_.back(); }

  //@ requires size() > 0
  //@ ensures size() == old(size()) - 1 && capacity() == old(capacity())
  //@ ensures forall i :: 0 <= i < size() ==> at(i) == old(at(i))
  //@ ensures size() > 0 ==> top() == at(size() - 1)
  void pop() { items_.pop_back(); }

  // A const reference to an element is its value.
  //@ requires i < size()
  //@ ensures result == items_[i]
  const Point& at(size_t i) const { return items_[i]; }

 private:
  std::vector<Point> items_;
  size_t capacity_;
};

//@ ensures result == 7
int32_t last_y() {
  Points s(2);
  s.push(Point{1, 2});
  s.push(Point{5, 7});
  return s.top().y;
}

//@ ensures result == 2
int32_t after_pop() {
  Points s(3);
  s.push(Point{1, 2});
  s.push(Point{5, 7});
  s.pop();
  return s.top().y;
}

//@ ensures result == 5
int32_t first_x() {
  Points s(3);
  s.push(Point{5, 7});
  s.push(Point{1, 2});
  return s.at(0).x;
}
