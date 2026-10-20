#include <cstdint>
#include <memory>
#include <utility>

// The forms of a unique_ptr of an interface that have no rule yet, decision 0168.
struct Shape {
  virtual ~Shape() = default;
  //@ ensures result >= 1
  virtual int32_t area() const = 0;
};

class Open : public Shape {
 public:
  //@ ensures result == 1
  int32_t area() const override { return 1; }
};

class Square final : public Shape {
 public:
  //@ ensures result == 4
  int32_t area() const override { return 4; }
};

class Two final : public Shape {
 public:
  //@ ensures result == 2
  int32_t area() const override {
    int32_t n = 2;
    return n;
  }
};

//@ requires p != nullptr
//@ ensures result >= 1
int32_t read(const std::unique_ptr<Shape>& p) {
  return p->area();
}

std::unique_ptr<Shape> open() {
  return std::make_unique<Open>();
}

std::unique_ptr<Shape> two() {
  return std::make_unique<Two>();
}

int32_t owned() {
  std::unique_ptr<Square> q = std::make_unique<Square>();
  return 4;
}

int32_t moved() {
  std::unique_ptr<Shape> q = std::make_unique<Square>();
  return read(std::move(q));
}

std::unique_ptr<Shape> local() {
  std::unique_ptr<Shape> s = std::make_unique<Square>();
  return s;
}
