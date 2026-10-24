#include <cstdint>

// A member function that writes its object and returns `*this`, and a chain of such calls, decision 0183.
class Counter {
 public:
  //@ ensures total() == 0
  Counter() : total_(0) {}

  //@ requires 0 <= n && n <= 100 && 0 <= total() && total() <= 1000
  //@ ensures total() == old(total()) + n
  Counter& add(int32_t n) {
    total_ += n;
    return *this;
  }

  //@ requires 0 <= total() && total() <= 500
  //@ ensures total() == old(total()) * 2
  Counter& twice() {
    if (total_ == 0) {
      return *this;
    }
    total_ *= 2;
    return *this;
  }

  //@ ensures result == total_
  int32_t total() const { return total_; }

 private:
  int32_t total_;
};

// A chain on a local, as a statement.
//@ ensures result == 3
int32_t on_local() {
  Counter c;
  c.add(1).add(2);
  return c.total();
}

// A chain on a temporary, in a return.
//@ ensures result == 7
int32_t on_temporary() {
  return Counter().add(3).add(4).total();
}

// A chain in the start value of a local.
//@ ensures result == 15
int32_t in_local() {
  int32_t v = Counter().add(5).add(5).total();
  return v + 5;
}

// A chain on a reference parameter.
//@ requires 0 <= c.total() && c.total() <= 900
//@ modifies c
//@ ensures c.total() == old(c.total()) + 2
void bump(Counter& c) {
  c.add(1).add(1);
}

// The steps run in the order of the source, and the argument of a step runs after the step before it. A step can return in a
// branch.
//@ ensures result == 4
int32_t in_order() {
  Counter c;
  c.add(1).twice().add(c.total());
  return c.total();
}

// Two temporaries in one function.
//@ ensures result == 3
int32_t two_temporaries() {
  int32_t a = Counter().add(1).total();
  int32_t b = Counter().add(2).total();
  return a + b;
}
