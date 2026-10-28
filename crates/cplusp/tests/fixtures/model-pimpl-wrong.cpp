#include <cstdint>
#include <memory>

// Claims about a pointer to implementation that do not hold, decision 0197.
struct Cell {
  int32_t v;
  //@ ensures v == b
  explicit Cell(int32_t b) : v(b) {}
};

class Box {
 public:
  //@ ensures has() && value() == k + 1
  explicit Box(int32_t k) : c_(std::make_unique<Cell>(k)) {}

  // The move leaves other null.
  //@ requires other.has()
  //@ modifies other
  //@ ensures other.has()
  Box(Box&& other) noexcept : c_(std::move(other.c_)) {}

  //@ ensures true
  ~Box();

  //@ ensures result == (c_ != nullptr)
  bool has() const { return c_ != nullptr; }

  //@ requires has()
  //@ ensures result == c_->v
  int32_t value() const { return c_->v; }

  // No requires line, so the pointer may be null.
  //@ ensures true
  void put(int32_t x) { c_->v = x; }

 private:
  std::unique_ptr<Cell> c_;
};

Box::~Box() = default;

// A later value of the init list reads other.c_ after the move, decision 0198. It is null there.
class Held {
 public:
  //@ ensures has()
  Held() : c_(std::make_unique<Cell>(1)), h_(true) {}

  //@ requires other.has()
  //@ modifies other
  //@ ensures h_
  Held(Held&& other) noexcept : c_(std::move(other.c_)), h_(other.c_ != nullptr) {}

  //@ ensures true
  ~Held();

  //@ ensures result == (c_ != nullptr)
  bool has() const { return c_ != nullptr; }

 private:
  std::unique_ptr<Cell> c_;
  bool h_;
};

Held::~Held() = default;

class Read {
 public:
  //@ ensures true
  Read() : c_(std::make_unique<Cell>(1)), n_(0) {}

  //@ requires other.c_ != nullptr
  //@ modifies other
  //@ ensures true
  Read(Read&& other) noexcept : c_(std::move(other.c_)), n_(other.c_->v) {}

  //@ ensures true
  ~Read();

 private:
  std::unique_ptr<Cell> c_;
  int32_t n_;
};

Read::~Read() = default;
