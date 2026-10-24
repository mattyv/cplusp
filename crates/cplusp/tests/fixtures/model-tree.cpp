#include <cstdint>
#include <memory>
#include <utility>

// A node that the code makes, writes through its pointer and gives away, decision 0186.
struct Cell {
  int32_t value = 7;
  int32_t count = 0;
  bool on = false;
  std::unique_ptr<Cell> next;
};

// Each field has its start value: its initializer, or null for a unique_ptr with none.
//@ ensures result != nullptr && result->value == 7 && result->count == 0 && !result->on && result->next == nullptr
std::unique_ptr<Cell> fresh() {
  std::unique_ptr<Cell> c = std::make_unique<Cell>();
  return c;
}

// A write through the pointer, and a read of the field it wrote.
//@ requires -1000 <= v && v <= 1000
//@ ensures result != nullptr && result->value == v + 1 && result->count == 0 && result->next == nullptr
std::unique_ptr<Cell> set(int32_t v) {
  std::unique_ptr<Cell> c = std::make_unique<Cell>();
  c->value = v;
  c->value = c->value + 1;
  return c;
}

// A parameter by value moves into a field.
//@ requires tail != nullptr
//@ ensures result != nullptr && result->next != nullptr && result->value == 7
std::unique_ptr<Cell> link(std::unique_ptr<Cell> tail) {
  std::unique_ptr<Cell> c = std::make_unique<Cell>();
  c->next = std::move(tail);
  return c;
}

//@ ensures result == true
bool take(std::unique_ptr<Cell> p) {
  return true;
}

// A parameter by value moves in a call that stands alone.
//@ ensures result == true
bool pass(std::unique_ptr<Cell> p) {
  const bool r = take(std::move(p));
  return r;
}

// The return of a parameter by value moves it.
//@ requires p != nullptr
//@ ensures result != nullptr && result->value == p->value
std::unique_ptr<Cell> back(std::unique_ptr<Cell> p) {
  return p;
}

// A local moves into a field, and the local that holds it moves on.
//@ ensures result == 8
int32_t chain() {
  std::unique_ptr<Cell> a = set(7);
  std::unique_ptr<Cell> b = std::make_unique<Cell>();
  b->next = std::move(a);
  std::unique_ptr<Cell> c = std::move(b);
  return c->next->value;
}

// A moved parameter is null, as C++ says.
//@ ensures result == true
bool gone(std::unique_ptr<Cell> p) {
  std::unique_ptr<Cell> c = std::make_unique<Cell>();
  c->next = std::move(p);
  return p == nullptr;
}
