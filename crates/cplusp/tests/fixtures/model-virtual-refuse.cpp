#include <cstdint>

// A class over an interface that is not final, a final class with no override, an override with no function in the model, a pointer
// to an interface, and an interface with two virtual functions of one name, decision 0165.
class Shape {
 public:
  virtual ~Shape() = default;
  //@ ensures result >= 3
  virtual int32_t corners() const = 0;
};

class Open : public Shape {
 public:
  //@ ensures result == 5
  int32_t corners() const override { return 5; }
};

class Half final : public Shape {
 public:
  int32_t sides() const { return 2; }
};

class Two final : public Shape {
 public:
  //@ ensures result == 4
  int32_t corners() const override {
    int32_t n = 4;
    return n;
  }
};

//@ ensures result >= 3
int32_t count(const Shape& shape) {
  return shape.corners();
}

//@ ensures result >= 3
int32_t via(const Shape* p) {
  return p->corners();
}

// Two virtual functions of one name have no rule yet.
class Sound {
 public:
  virtual ~Sound() = default;
  //@ ensures result >= 1
  virtual int32_t pitch() const = 0;
  //@ ensures result >= 1
  virtual int32_t pitch(int32_t up) const = 0;
};

class Bell final : public Sound {
 public:
  //@ ensures result == 2
  int32_t pitch() const override { return 2; }
  //@ ensures result == 2
  int32_t pitch(int32_t up) const override { return 2; }
};

// A class that is not final is no type of the model, so a call on it is never a call of one override.
//@ ensures result >= 3
int32_t open_corners(const Open& o) {
  return o.corners();
}

// A call with the name of the class runs no override.
//@ ensures result >= 3
int32_t base_count(const Shape& s) {
  return s.Shape::corners();
}

// A pure virtual function with a body has no rule yet.
int32_t Sound::pitch() const { return 1; }
