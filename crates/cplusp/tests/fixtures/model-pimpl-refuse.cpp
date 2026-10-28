#include <cstdint>
#include <memory>
#include <vector>

// The forms of a pointer to implementation that have no rule, decision 0197.
struct Cell {
  int32_t v;
  explicit Cell(int32_t b) : v(b) {}
};

// A move constructor = default of a struct with a vector field.
class Bag {
 public:
  //@ ensures true
  Bag() : c_(std::make_unique<Cell>(1)) {}

  //@ modifies other
  //@ ensures true
  Bag(Bag&& other) noexcept;

  //@ ensures true
  ~Bag();

 private:
  std::unique_ptr<Cell> c_;
  std::vector<int32_t> items_;
};

Bag::Bag(Bag&& other) noexcept = default;

Bag::~Bag() = default;

// A write through a unique_ptr field of a parameter.
struct Holder {
  std::unique_ptr<Cell> c;
};

//@ modifies h
//@ ensures true
void poke(Holder& h) {
  h.c->v = 1;
}

// A move constructor with a second parameter, decision 0198.
class Two {
 public:
  //@ ensures true
  Two() : c_(std::make_unique<Cell>(1)) {}

  //@ modifies other
  //@ ensures true
  Two(Two&& other, int32_t z = 0) noexcept : c_(std::move(other.c_)) {}

  //@ ensures true
  ~Two();

 private:
  std::unique_ptr<Cell> c_;
};

Two::~Two() = default;
