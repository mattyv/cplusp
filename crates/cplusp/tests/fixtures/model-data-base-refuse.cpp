#include <cstdint>

// What a base with data has no rule for yet, decision 0201.
class Tag {
 public:
  //@ ensures id() == id
  explicit Tag(uint32_t id) : id_(id) {}
  //@ ensures result == id_
  uint32_t id() const { return id_; }
  //@ ensures id() == n
  void rename(uint32_t n) { id_ = n; }

 private:
  uint32_t id_;
};

struct Spot {
  int32_t x;
};

class Box final : public Tag {
 public:
  //@ ensures this->id() == id
  explicit Box(uint32_t id) : Tag(id) {}
};

struct Pixel final : Spot {
  //@ ensures true
  int32_t left() const { return x; }
};

//@ ensures result == t.id()
uint32_t id_of(const Tag& t) {
  return t.id();
}

//@ ensures result == 4
uint32_t through_base() {
  Box b(4);
  return id_of(b);
}

//@ modifies b
//@ ensures b.id() == 2
void rename_box(Box& b) {
  b.rename(2);
}
