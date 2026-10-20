#include <cstdint>

// A caller that claims more than the interface, a contract call with no valid(), and an object that is not valid, decision 0166.
struct Strategy {
  virtual ~Strategy() = default;
  virtual bool valid() const = 0;
  //@ requires valid() && 0 <= x && x <= 1000
  //@ ensures 0 <= result && result <= 2000
  virtual int32_t apply(int32_t x) const = 0;
};

class Never final : public Strategy {
 public:
  //@ ensures result == false
  bool valid() const override { return false; }
  //@ requires valid() && 0 <= x && x <= 1000
  //@ ensures result == 0
  int32_t apply(int32_t x) const override { return 0; }
};

//@ requires s.valid() && 0 <= x && x <= 1000
//@ ensures result <= 1000
int32_t once(const Strategy& s, int32_t x) {
  return s.apply(x);
}

//@ requires 0 <= x && x <= 1000
//@ ensures s.apply(x) >= 0 ==> result == 0
int32_t unchecked(const Strategy& s, int32_t x) {
  return 0;
}

//@ ensures result <= 2000
int32_t demo() {
  const Never n;
  return once(n, 4);
}
