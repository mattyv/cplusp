#include <cstdint>
// A const virtual function that gives a value and writes a parameter has no rule yet, decision 0225.
class Sink {
 public:
  //@ ensures total_ == 0
  Sink() : total_(0) {}

  //@ requires total_ < 1000
  //@ requires 0 <= n
  //@ requires n < 100
  //@ ensures total_ == old(total_) + n
  void add(int32_t n) { total_ = total_ + n; }

  //@ ensures result == total_
  int32_t total() const { return total_; }

 private:
  int32_t total_;
};

class Shape {
 public:
  virtual ~Shape() = default;
  //@ requires s.total() < 1000
  //@ modifies s
  //@ ensures result == 7
  //@ ensures s.total() == old(s.total()) + 7
  virtual int32_t area(Sink& s) const = 0;
};

class Square final : public Shape {
 public:
  //@ ensures true
  Square() {}
  //@ requires s.total() < 1000
  //@ modifies s
  //@ ensures result == 7
  //@ ensures s.total() == old(s.total()) + 7
  int32_t area(Sink& s) const override {
    s.add(7);
    return 7;
  }
};

//@ requires k.total() == 0
//@ modifies k
//@ ensures k.total() == 0
//@ ensures result == 7
int32_t twice(const Shape& sh, Sink& k) {
  int32_t a = sh.area(k);
  return a;
}
