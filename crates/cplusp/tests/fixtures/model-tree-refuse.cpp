#include <cstdint>
#include <memory>
#include <utility>

// The forms of a node that the code makes that have no rule yet, decision 0186.
struct Cell {
  int32_t value = 7;
  std::unique_ptr<Cell> next;
};

enum class Color { red, green };

struct Tagged {
  Color color = Color::red;
};

int32_t seed() {
  return 3;
}

struct Seeded {
  int32_t value = seed();
};

//@ ensures true
int32_t through_kept(std::unique_ptr<Cell> p) {
  p->value = 1;
  return 0;
}

//@ ensures true
int32_t compound() {
  std::unique_ptr<Cell> c = std::make_unique<Cell>();
  c->value += 1;
  return 0;
}

//@ ensures true
int32_t deep() {
  std::unique_ptr<Cell> c = std::make_unique<Cell>();
  c->next = std::make_unique<Cell>();
  c->next->value = 1;
  return 0;
}

//@ ensures true
int32_t tagged() {
  std::unique_ptr<Tagged> t = std::make_unique<Tagged>();
  return 0;
}

//@ ensures true
int32_t seeded() {
  std::unique_ptr<Seeded> s = std::make_unique<Seeded>();
  return 0;
}

//@ ensures true
int32_t swap_in() {
  std::unique_ptr<Cell> a = std::make_unique<Cell>();
  std::unique_ptr<Cell> b = std::make_unique<Cell>();
  a = std::move(b);
  return 0;
}

//@ ensures true
std::unique_ptr<Cell> none() {
  return nullptr;
}

// A start value that overflows is no constant expression.
struct Over {
  int32_t value = 2147483647 + 1;
};

//@ ensures true
int32_t over() {
  std::unique_ptr<Over> o = std::make_unique<Over>();
  return 0;
}

// A start value that writes a global is no constant expression.
int32_t g = 0;

struct Side {
  int32_t value = (g = 9, 4);
};

//@ modifies g
//@ ensures true
int32_t side() {
  std::unique_ptr<Side> s = std::make_unique<Side>();
  return 0;
}

// A scalar field with no initializer.
struct Bare {
  int32_t value;
};

//@ ensures true
int32_t bare() {
  std::unique_ptr<Bare> b = std::make_unique<Bare>();
  return 0;
}

// A parameter that moves only in a return stays a parameter.
//@ ensures true
std::unique_ptr<Cell> only_return(std::unique_ptr<Cell> p) {
  p->value = 3;
  return p;
}
