#include <cstdint>

// A final class over a base class with data and an interface, decision 0201.
class Tag {
 public:
  //@ ensures id() == id
  explicit Tag(uint32_t id) : id_(id) {}
  //@ ensures result == id_
  uint32_t id() const { return id_; }

 private:
  uint32_t id_;
};

class Sized {
 public:
  virtual ~Sized() = default;
  virtual uint32_t size() const = 0;
};

class Box final : public Tag, public Sized {
 public:
  //@ ensures this->id() == id && size() == size
  Box(uint32_t id, uint32_t size) : Tag(id), size_(size) {}
  //@ ensures result == size_
  uint32_t size() const override { return size_; }
  //@ ensures result == id() + 1
  uint64_t next_id() const { return id() + uint64_t{1}; }

 private:
  uint32_t size_;
};

// A base with data and no interface.
struct Plain : Tag {
  //@ ensures id() == 3
  Plain() : Tag(3) {}
};

//@ ensures result == s.size()
uint64_t size_of(const Sized& s) {
  return s.size();
}

//@ ensures result == b.id() + b.size()
uint64_t both(const Box& b) {
  return b.id() + size_of(b);
}

//@ ensures result == 21
uint64_t demo() {
  Box b(5, 7);
  Plain p;
  return both(b) + b.next_id() + p.id();
}
