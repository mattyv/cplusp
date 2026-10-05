#include <cstddef>
#include <cstdint>
#include <vector>

// A fixed-capacity queue over a vector. The head is the index of the oldest element and the count is how many are in. The next push goes
// to (head + count) % capacity and a pop moves the head to (head + 1) % capacity, so the indexes wrap and nothing is ever moved or grown.
// The capacity is a run-time value, as in stack_template, and valid() keeps it at most a million, so no sum below can overflow.
// The contracts use the implicit this, decision 0028. at(i) is the i-th oldest element, and the contracts of push and pop say what it
// is before and after, so a caller proves the order of its elements from the contracts alone.
class RingBuffer {
 public:
  //@ requires 0 < capacity && capacity <= 1000000
  //@ ensures valid() && size() == 0 && this->capacity() == capacity
  explicit RingBuffer(size_t capacity) : items_(capacity, 0), head_(0), count_(0), capacity_(capacity) {}

  //@ ensures result == (0 < capacity_ && capacity_ <= 1000000 && items_.size() == capacity_ && head_ < capacity_ && count_ <= capacity_)
  bool valid() const { return 0 < capacity_ && capacity_ <= 1000000 && items_.size() == capacity_ && head_ < capacity_ && count_ <= capacity_; }

  //@ requires valid()
  //@ ensures result == count_
  size_t size() const { return count_; }

  //@ requires valid()
  //@ ensures result == capacity_
  size_t capacity() const { return capacity_; }

  //@ requires valid() && i < size()
  //@ ensures result == items_[(head_ + i) % capacity_]
  int32_t at(size_t i) const { return items_.at((head_ + i) % capacity_); }

  //@ requires valid() && size() < capacity()
  //@ ensures valid() && capacity() == old(capacity()) && size() == old(size()) + 1
  //@ ensures at(size() - 1) == x
  //@ ensures forall i :: 0 <= i < old(size()) ==> at(i) == old(at(i))
  void push(int32_t x) {
    items_[(head_ + count_) % capacity_] = x;
    count_ += 1;
  }

  //@ requires valid() && size() > 0
  //@ ensures valid() && capacity() == old(capacity()) && size() == old(size()) - 1
  //@ ensures result == old(at(0))
  //@ ensures forall i :: 0 <= i < size() ==> at(i) == old(at(i + 1))
  int32_t pop() {
    int32_t oldest = items_[head_];
    head_ = (head_ + 1) % capacity_;
    count_ -= 1;
    return oldest;
  }

 private:
  std::vector<int32_t> items_;
  size_t head_;
  size_t count_;
  size_t capacity_;
};

// The third push lands on the slot the first pop freed, so the indexes wrap. The elements still come out in the order they went in.
//@ ensures result == 123
int32_t first_in_first_out() {
  RingBuffer r(2);
  r.push(1);
  r.push(2);
  int32_t a = r.pop();
  r.push(3);
  int32_t b = r.pop();
  int32_t c = r.pop();
  return a * 100 + b * 10 + c;
}
