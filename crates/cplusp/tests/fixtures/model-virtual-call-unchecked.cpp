#include <cstdint>

// A call that upcasts a class whose check is refused, decision 0166.
struct Shape {
  virtual ~Shape() = default;
  //@ ensures result >= 3
  virtual int32_t corners() const = 0;
};

class Two final : public Shape {
 public:
  //@ ensures result == 4
  int32_t corners() const override {
    int32_t n = 0; n = 4;
    return n;
  }
};

//@ ensures result >= 3
int32_t count(const Shape& s) {
  return s.corners();
}

//@ ensures result >= 3
int32_t demo() {
  const Two t;
  return count(t);
}
