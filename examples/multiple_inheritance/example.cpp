#include <cstdint>

// One concrete base and any number of pure interfaces. An interface has only pure virtual functions and a virtual destructor,
// so it carries no data. The function reads the object through each interface, and the sum cannot overflow in 64 bits.
class Item {
 public:
  //@ ensures id() == id
  explicit Item(uint32_t id) : id_(id) {}
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

class Weighed {
 public:
  virtual ~Weighed() = default;
  virtual uint32_t weight() const = 0;
};

class Crate : public Item, public Sized, public Weighed {
 public:
  //@ ensures this->id() == id && size_ == size && weight_ == weight
  Crate(uint32_t id, uint32_t size, uint32_t weight) : Item(id), size_(size), weight_(weight) {}
  //@ ensures result == size_
  uint32_t size() const override { return size_; }
  //@ ensures result == weight_
  uint32_t weight() const override { return weight_; }

 private:
  uint32_t size_;
  uint32_t weight_;
};

//@ ensures result == c.size() + c.weight()
uint64_t both(const Crate& c) {
  const Sized& s = c;
  const Weighed& w = c;
  return uint64_t{s.size()} + w.weight();
}
