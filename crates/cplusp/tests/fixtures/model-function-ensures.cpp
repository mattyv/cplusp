#include <cstdint>

// The function of a pure member function keeps its ensures lines, so a caller and the check of an override read them, decision 0213.

struct Concept {
  virtual ~Concept() = default;
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures 0 <= result <= 1000000
  virtual int32_t area() const = 0;
};

template <typename T>
class Model final : public Concept {
 public:
  //@ requires value.valid()
  //@ ensures valid()
  explicit Model(T value) : value_(value) {}

  //@ ensures result == value_.valid()
  bool valid() const override { return value_.valid(); }

  //@ requires valid()
  //@ ensures result == value_.area()
  int32_t area() const override { return value_.area(); }

 private:
  T value_;
};

struct Square {
  int32_t side;

  //@ ensures result == (0 <= side && side <= 1000)
  bool valid() const { return 0 <= side && side <= 1000; }

  //@ requires valid()
  //@ ensures 0 <= result <= 1000000 && result == side * side
  int32_t area() const {
    //@ apply MulBound(side, side, 1000, 1000)
    return side * side;
  }
};

template class Model<Square>;

//@ requires 0 <= s <= 1000
//@ ensures 0 <= result <= 1000000
int32_t one(int32_t s) {
  const Model<Square> m(Square{s});
  return m.area();
}
