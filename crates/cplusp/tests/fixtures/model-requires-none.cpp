#include <cstdint>
// A requires line that no input meets proves, and a call of it in verified code does not, decision 0221.
struct Poker {
  virtual ~Poker() = default;
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures result == 1 && result == 2
  virtual int32_t poke() const = 0;
};

class Dead final : public Poker {
 public:
  //@ ensures result == false
  bool valid() const override { return false; }
  //@ requires valid()
  //@ ensures result == 1 && result == 2
  int32_t poke() const override { return 0; }
};

//@ requires p.valid()
//@ ensures result == 42
int32_t quiet(const Poker& p) {
  int32_t k = p.poke();
  return 0;
}

//@ requires false
//@ ensures result == 42
int32_t quiet0() { return 0; }
