#include <cstdint>
#include <memory>

// Claims about a pointer to implementation that do not hold, decision 0197.
struct Cell {
  int32_t v;
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
