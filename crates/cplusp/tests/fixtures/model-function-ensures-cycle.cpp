#include <cstdint>

// An ensures line that calls a function stays on the method, so two functions whose lines call each other prove, decision 0215.

class Bag {
 public:
  //@ ensures result == (0 <= size() && size() <= 10)
  bool valid() const { return 0 <= n_ && n_ <= 10; }
  //@ ensures valid() ==> result <= 10
  int32_t size() const { return n_; }

 private:
  int32_t n_;
};

//@ requires b.valid()
//@ ensures result <= 11
int32_t one_more(const Bag& b) { return b.size() + 1; }
