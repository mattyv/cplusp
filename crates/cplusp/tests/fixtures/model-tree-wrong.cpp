#include <cstdint>
#include <memory>
#include <utility>

// Claims about a node that the code makes that do not hold, decision 0186.
struct Cell {
  int32_t value = 7;
  int32_t count = 0;
  std::unique_ptr<Cell> next;
};

// The start value is the initializer, not zero.
//@ ensures result != nullptr && result->value == 0
std::unique_ptr<Cell> fresh() {
  std::unique_ptr<Cell> c = std::make_unique<Cell>();
  return c;
}

// A write sets one field and keeps the others.
//@ ensures result != nullptr && result->count == 5
std::unique_ptr<Cell> set() {
  std::unique_ptr<Cell> c = std::make_unique<Cell>();
  c->value = 5;
  return c;
}

// The field holds the moved pointer, so it is not null.
//@ requires tail != nullptr
//@ ensures result != nullptr && result->next == nullptr
std::unique_ptr<Cell> link(std::unique_ptr<Cell> tail) {
  std::unique_ptr<Cell> c = std::make_unique<Cell>();
  c->next = std::move(tail);
  return c;
}

// The parameter can be null, so the write through it can fail.
//@ ensures true
int32_t poke(std::unique_ptr<Cell> p) {
  std::unique_ptr<Cell> c = std::move(p);
  c->value = 1;
  return 0;
}

// A moved parameter does not keep its value.
//@ requires p != nullptr
//@ ensures result == true
bool kept(std::unique_ptr<Cell> p) {
  std::unique_ptr<Cell> c = std::move(p);
  return p != nullptr;
}

// A move in a branch leaves the parameter null after the branch.
//@ requires p != nullptr
//@ ensures result == true
bool branch(std::unique_ptr<Cell> p, bool b) {
  if (b) {
    std::unique_ptr<Cell> c = std::move(p);
  }
  return p != nullptr;
}
