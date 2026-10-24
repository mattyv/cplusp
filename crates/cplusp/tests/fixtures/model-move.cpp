#include <cstdint>
#include <utility>

// A constructor with a body, a move constructor, a `T&&` parameter and `std::move` of a struct, decision 0179.
int32_t open_count = 0;

class Token {
 public:
  // The body runs after the init list. It writes a global and declares a local.
  //@ requires 0 <= open_count < 1000
  //@ modifies open_count
  //@ ensures live() && id() == old(open_count) && open_count == old(open_count) + 1
  Token() : live_(true), id_(open_count) {
    int32_t next = open_count + 1;
    open_count = next;
  }

  Token(const Token&) = delete;
  Token& operator=(const Token&) = delete;
  Token& operator=(Token&&) = delete;

  // The init list reads `other` before the body writes it.
  //@ requires other.live()
  //@ modifies other
  //@ ensures live() && id() == old(other.id()) && !other.live() && other.id() == old(other.id())
  Token(Token&& other) noexcept : live_(other.live_), id_(other.id_) { other.live_ = false; }

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

// The function owns what it moves out of `t`. The token it moves into a local dies at its end.
//@ requires t.live() && 0 < open_count <= 1000
//@ modifies open_count, t
//@ ensures open_count == old(open_count) - 1 && !t.live() && result == old(t.id())
int32_t take(Token&& t) {
  Token owned = std::move(t);
  return owned.id();
}

// The caller's token is closed after the call, so its destructor releases nothing.
//@ requires 0 <= open_count < 1000
//@ modifies open_count
//@ ensures open_count == old(open_count) && result == old(open_count)
int32_t hand_over() {
  Token t;
  return take(std::move(t));
}

// A move into a local of the same block. The moved-from token dies too, and only the new token releases.
//@ requires 0 <= open_count < 1000
//@ modifies open_count
//@ ensures open_count == old(open_count) && result
bool move_here() {
  Token a;
  Token b = std::move(a);
  return b.live();
}

// A move that keeps the source open. The move constructor opens a second count, so both twins release.
class Twin {
 public:
  //@ requires 0 <= open_count < 1000
  //@ modifies open_count
  //@ ensures live() && open_count == old(open_count) + 1
  Twin() : live_(true) { open_count += 1; }

  Twin(const Twin&) = delete;
  Twin& operator=(const Twin&) = delete;
  Twin& operator=(Twin&&) = delete;

  //@ requires other.live() && 0 <= open_count < 1000
  //@ modifies open_count, other
  //@ ensures live() && other.live() && open_count == old(open_count) + 1
  Twin(Twin&& other) noexcept : live_(other.live_) { open_count += 1; }

  //@ requires 0 <= open_count <= 1000
  //@ modifies open_count
  //@ ensures open_count == old(open_count) - (old(live()) ? 1 : 0)
  ~Twin() {
    if (live_) {
      open_count -= 1;
    }
  }

  //@ ensures result == live_
  bool live() const { return live_; }

 private:
  bool live_;
};

// The moved-from twin stays open. The new twin dies at the end of the inner block, and the moved-from twin at the end of
// the outer block.
//@ requires 0 <= open_count < 999
//@ modifies open_count
//@ ensures open_count == old(open_count) && result == old(open_count) + 1
int32_t both_die() {
  int32_t inside = 0;
  {
    Twin a;
    {
      Twin b = std::move(a);
    }
    inside = open_count;
  }
  return inside;
}
