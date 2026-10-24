#include <cstdint>

// A reference result that is not `*this`, and the object of a chain used other than as the object of a call, decision 0183.
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

  //@ requires 0 <= total() && total() <= 1000
  //@ modifies o
  //@ ensures true
  Counter& other(Counter& o) {
    total_ += 1;
    return o;
  }

  //@ ensures result == total_
  int32_t total() const { return total_; }

 private:
  int32_t total_;
};

//@ ensures result == c.total()
int32_t read(const Counter& c) {
  return c.total();
}

//@ ensures result == 1
int32_t passed() {
  Counter c;
  return read(c.add(1));
}

int32_t open_handles = 0;

// A step that can end with no return, a step that returns a copy, and a step with one return that is not `*this`.
class Tally {
 public:
  //@ ensures total() == 0
  Tally() : total_(0) {}

  //@ requires 0 <= total() && total() <= 1000
  //@ ensures total() == old(total()) + 1
  Tally& lost() {
    total_ += 1;
  }

  //@ requires 0 <= n && n <= 100 && 0 <= total() && total() <= 1000
  //@ ensures total() == old(total()) + n
  Tally copy_add(int32_t n) {
    total_ += n;
    return *this;
  }

  //@ requires 0 <= total() && total() <= 1000
  //@ modifies o
  //@ ensures true
  Tally& pick(Tally& o, bool b) {
    total_ += 1;
    if (b) {
      return o;
    }
    return *this;
  }

  //@ ensures result == total_
  int32_t total() const { return total_; }

 private:
  int32_t total_;
};

// A temporary of a struct with a destructor.
class Guard {
 public:
  //@ ensures total() == 0
  Guard() : total_(0) {}

  //@ requires open_handles > 0
  //@ modifies open_handles
  //@ ensures open_handles == old(open_handles) - 1
  ~Guard() { open_handles -= 1; }

  //@ requires 0 <= n && n <= 100 && 0 <= total() && total() <= 1000
  //@ ensures total() == old(total()) + n
  Guard& add(int32_t n) {
    total_ += n;
    return *this;
  }

  //@ ensures result == total_
  int32_t total() const { return total_; }

 private:
  int32_t total_;
};

//@ requires open_handles > 0
//@ modifies open_handles
//@ ensures result == 1
int32_t on_a_guard() {
  return Guard().add(1).total();
}

// A chain where C++ may not run it once, or inside an expression.
//@ ensures result == a
bool on_the_right(bool a) {
  Counter c;
  return a && c.add(1).total() == 1;
}

//@ ensures result == 3
int32_t in_a_loop() {
  Counter c;
  while (c.add(1).total() < 3) {
  }
  return c.total();
}

//@ ensures result == 1
int32_t in_a_branch(bool a) {
  Counter c;
  if (a) {
    return 1;
  } else if (c.add(1).total() == 1) {
    return c.total();
  }
  return 1;
}

//@ ensures result == 2
int32_t in_an_operand() {
  Counter c;
  return c.add(1).total() + 1;
}

//@ ensures result == 0
int32_t in_a_step() {
  Counter c;
  for (int32_t i = 0; i < 0; c.add(1).add(1)) {
  }
  return c.total();
}
