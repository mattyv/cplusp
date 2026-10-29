#include <cstdint>

// Overrides whose body is no pure body: a write to a local, and a call of an own member function that is not plain, decisions 0172, 0189.
struct Component {
  virtual ~Component() = default;
  virtual bool valid() const = 0;
  //@ requires valid() && 0 <= x <= 1000
  //@ ensures 0 <= result <= 1000000
  virtual int32_t cost(int32_t x) const = 0;
};

class Written final : public Component {
 public:
  //@ ensures result == true
  bool valid() const override { return true; }

  //@ requires valid() && 0 <= x <= 1000
  //@ ensures result == x
  int32_t cost(int32_t x) const override {
    int32_t t = x;
    t = t + 0;
    return t;
  }
};

class Own final : public Component {
 public:
  //@ ensures result == 0
  int32_t ok() const { return cost(0); }

  //@ ensures result
  bool valid() const override { return ok() == 0; }

  //@ requires valid() && 0 <= x <= 1000
  //@ ensures result == 0
  int32_t cost(int32_t x) const override { return 0; }
};
