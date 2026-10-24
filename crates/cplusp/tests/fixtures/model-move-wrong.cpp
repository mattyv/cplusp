#include <cstdint>
#include <utility>

// A move constructor that leaves the source open, a claim that the init list sees the body's write, and a caller that forgets
// the release, decision 0179.
int32_t open_count = 0;

class Token {
 public:
  //@ requires 0 <= open_count < 1000
  //@ modifies open_count
  //@ ensures live() && open_count == old(open_count) + 1
  Token() : live_(true), id_(7) { open_count += 1; }

  Token(const Token&) = delete;
  Token& operator=(const Token&) = delete;
  Token& operator=(Token&&) = delete;

  // The body does not close the source.
  //@ requires other.live()
  //@ modifies other
  //@ ensures live() && !other.live()
  Token(Token&& other) noexcept : live_(other.live_), id_(other.id_) {}

  //@ requires 0 <= open_count <= 1000
  //@ modifies open_count
  //@ ensures open_count == old(open_count) - (old(live()) ? 1 : 0)
  ~Token() {
    if (live_) {
      open_count -= 1;
    }
  }

  //@ ensures result == live_
  bool live() const { return live_; }

  //@ ensures result == id_
  int32_t id() const { return id_; }

 private:
  bool live_;
  int32_t id_;
};

class Cell {
 public:
  //@ ensures value() == v
  explicit Cell(int32_t v) : value_(v) {}

  Cell(const Cell&) = delete;
  Cell& operator=(const Cell&) = delete;
  Cell& operator=(Cell&&) = delete;

  // The init list reads `other.value_` before the body sets it to 0, so the new cell holds the old value.
  //@ modifies other
  //@ ensures value() == 0
  Cell(Cell&& other) noexcept : value_(other.value_) { other.value_ = 0; }

  //@ ensures true
  ~Cell() {}

  //@ ensures result == value_
  int32_t value() const { return value_; }

 private:
  int32_t value_;
};

// The moved token dies at the return, so the count falls.
//@ requires t.live() && 0 < open_count <= 1000
//@ modifies open_count, t
//@ ensures open_count == old(open_count)
int32_t take(Token&& t) {
  Token owned = std::move(t);
  return owned.id();
}
