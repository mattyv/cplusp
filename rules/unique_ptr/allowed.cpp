#include <cstddef>
#include <utility>
#include <span>
#include <array>
#include <cstdint>
#include <memory>
#include <vector>

struct Command {
  virtual ~Command() = default;
  virtual void run() = 0;
  virtual int32_t peek() const = 0;
};

// A non-const container, so the owned commands may change.
//@ requires cmds.size() <= 1000
//@ requires forall i :: 0 <= i < cmds.size() ==> cmds[i] != nullptr
void run_all(std::vector<std::unique_ptr<Command>>& cmds) {
  for (size_t i = 0; i < cmds.size(); ++i) {
    cmds[i]->run();
  }
}

// A const container gives const access, and a const call is fine.
//@ requires cmds.size() > 0 && cmds[0] != nullptr
//@ ensures result == cmds[0]->peek()
int32_t peek_first(const std::vector<std::unique_ptr<Command>>& cmds) {
  return cmds[0]->peek();
}

//@ requires p != nullptr
//@ ensures result == p->peek()
int32_t peek_one(const std::unique_ptr<Command>& p) {
  return p->peek();
}

struct S {
  int32_t x = 0;
};

void mutate(int32_t& x) {
  x = 42;
}

// A read through a const handle is fine.
//@ requires p != nullptr
//@ ensures result == *p + 1
int32_t read_through(const std::unique_ptr<int32_t>& p) {
  return *p + 1;
}

// A write through a non-const handle is fine.
//@ requires p != nullptr
//@ ensures *p == 42
void write_through(std::unique_ptr<int32_t>& p) {
  *p = 42;
}

//@ requires p != nullptr
//@ ensures p->x == 42
void escape_through(std::unique_ptr<S>& p) {
  mutate(p->x);
}

// A read through a const handle by a const view, or by std::as_const, writes nothing.
//@ requires s.size() > 0
//@ ensures result == s[0]
int32_t first_of(std::span<const int32_t> s) {
  return s[0];
}

//@ requires p != nullptr
//@ ensures result == (*p)[0]
int32_t read_by_view(const std::unique_ptr<std::array<int32_t, 4>>& p) {
  return first_of(*p);
}

//@ requires p != nullptr
//@ ensures result == *p
int32_t read_as_const(const std::unique_ptr<int32_t>& p) {
  return std::as_const(*p);
}
