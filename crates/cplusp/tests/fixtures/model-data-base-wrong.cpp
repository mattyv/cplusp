#include <cstdint>

// A false claim through a member function of the base fails, decision 0201.
class Tag {
 public:
  //@ ensures id() == id
  explicit Tag(uint32_t id) : id_(id) {}
  //@ ensures result == id_
  uint32_t id() const { return id_; }

 private:
  uint32_t id_;
};

class Box final : public Tag {
 public:
  //@ ensures this->id() == id
  explicit Box(uint32_t id) : Tag(id) {}
  //@ ensures result == id()
  uint64_t next_id() const { return id() + uint64_t{1}; }
};

//@ ensures result == 6
uint64_t demo() {
  Box b(4);
  return b.id();
}
