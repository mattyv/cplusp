#include <cstdint>

// A contract of an interface calls another virtual function, a caller reads the interface in its contract, and a final class goes
// to a parameter of the interface, decision 0166.
struct Strategy {
  virtual ~Strategy() = default;
  virtual bool valid() const = 0;
  //@ requires valid() && 0 <= x && x <= 1000
  //@ ensures 0 <= result && result <= 2000
  virtual int32_t apply(int32_t x) const = 0;
};

class Doubled final : public Strategy {
 public:
  //@ ensures result == true
  bool valid() const override { return true; }
  //@ requires valid() && 0 <= x && x <= 1000
  //@ ensures result == x + x
  int32_t apply(int32_t x) const override { return x + x; }
};

class Shifted final : public Strategy {
 public:
  //@ requires 0 <= k && k <= 1000
  //@ ensures valid() && this->k_ == k
  explicit Shifted(int32_t k) : k_(k) {}
  //@ ensures result == (0 <= k_ && k_ <= 1000)
  bool valid() const override { return 0 <= k_ && k_ <= 1000; }
  //@ requires valid() && 0 <= x && x <= 1000
  //@ ensures result == x + k_
  int32_t apply(int32_t x) const override { return x + k_; }

 private:
  int32_t k_;
};

//@ requires s.valid() && 0 <= x && x < 1000
//@ ensures 0 <= result && result <= 4000 && result == s.apply(x) + s.apply(x + 1)
int32_t neighbours(const Strategy& s, int32_t x) {
  return s.apply(x) + s.apply(x + 1);
}

// 4 + 4 + 5 + 5 is 18, and 4 + 3 + 5 + 3 is 15.
//@ ensures result == 33
int32_t demo() {
  const Doubled d;
  const Shifted s(3);
  const int32_t a = neighbours(d, 4);
  const int32_t b = neighbours(s, 4);
  return a + b;
}
