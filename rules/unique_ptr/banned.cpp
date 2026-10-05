#include <cstdint>
#include <memory>
#include <vector>

struct Command {
  virtual ~Command() = default;
  virtual void run() = 0;
};

void run_first(const std::vector<std::unique_ptr<Command>>& cmds) {
  cmds[0]->run();  // BANNED
}

void run_one(const std::unique_ptr<Command>& p) {
  p->run();  // BANNED
}

void run_deref(const std::unique_ptr<Command>& p) {
  (*p).run();  // BANNED
}

struct S {
  int32_t x = 0;
};

void mutate(int32_t& x) {
  x = 42;
}

// A write through a const handle, in every spelling: an assignment, a member write, an increment, and a non-const binding.
void assign_through(const std::unique_ptr<int32_t>& p) {
  *p = 42;  // BANNED
}

void member_write_through(const std::unique_ptr<S>& p) {
  p->x = 42;  // BANNED
}

void increment_through(const std::unique_ptr<int32_t>& p) {
  (*p)++;  // BANNED
}

void escape_through(const std::unique_ptr<int32_t>& p) {
  mutate(*p);  // BANNED
}

void member_escape_through(const std::vector<std::unique_ptr<S>>& owners) {
  mutate(owners[0]->x);  // BANNED
}

// An array owner: a subscript through a const handle is a write through it too. The array type itself is outside the subset,
// so the one line carries both findings.
void array_write_through(const std::unique_ptr<int32_t[]>& p) { p[0] = 1; }  // BANNED also: unlisted
