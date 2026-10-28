#include <cstdint>
#include <memory>

// The pointer to implementation, decision 0197.
struct Cell {
  int32_t v;
  explicit Cell(int32_t b) : v(b) {}
};

class Box {
 public:
  //@ ensures has() && value() == k
  explicit Box(int32_t k) : c_(std::make_unique<Cell>(k)) {}

  //@ requires other.has()
  //@ modifies other
  //@ ensures has() && value() == old(other.value()) && !other.has()
  Box(Box&& other) noexcept : c_(std::move(other.c_)) {}

  //@ ensures true
  ~Box();

  //@ ensures result == (c_ != nullptr)
  bool has() const { return c_ != nullptr; }

  //@ requires has()
  //@ ensures result == c_->v
  int32_t value() const { return c_->v; }

  //@ requires has() && 0 <= x <= 1000 && 0 <= value() <= 1000
  //@ ensures has() && value() == old(value()) + x
  void add(int32_t x) { c_->v += x; }

  //@ requires has()
  //@ ensures has() && value() == x
  void put(int32_t x) { c_->v = x; }

 private:
  std::unique_ptr<Cell> c_;
};

Box::~Box() = default;

// A move constructor = default moves the unique_ptr and copies the scalar.
class Pair {
 public:
  //@ ensures has() && n_ == n
  explicit Pair(int32_t n) : c_(std::make_unique<Cell>(n)), n_(n) {}

  //@ requires other.has()
  //@ modifies other
  //@ ensures has() && n_ == old(other.n_) && !other.has()
  Pair(Pair&& other) noexcept;

  //@ ensures true
  ~Pair();

  //@ ensures result == (c_ != nullptr)
  bool has() const { return c_ != nullptr; }

  //@ ensures result == n_
  int32_t count() const { return n_; }

 private:
  std::unique_ptr<Cell> c_;
  int32_t n_;
};

Pair::Pair(Pair&& other) noexcept = default;

Pair::~Pair() = default;

//@ ensures result == 8
int32_t eight() {
  Box b(3);
  b.add(5);
  return b.value();
}

//@ ensures result == 6
int32_t moved() {
  Box a(3);
  Box b(std::move(a));
  b.put(6);
  return b.value();
}

//@ ensures result == 5
int32_t pair_moved() {
  Pair a(5);
  Pair b(std::move(a));
  return b.count();
}
