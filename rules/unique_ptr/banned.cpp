#include <algorithm>
#include <array>
#include <cstdint>
#include <memory>
#include <optional>
#include <span>
#include <vector>
#include <sys/uio.h>

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

// A write through a const handle inside a template, judged at its instantiation, decision 0036.
template <class T>
void poke(const std::unique_ptr<T>& p) {
  *p = 42;  // BANNED
}

void use_poke(const std::unique_ptr<int32_t>& p) {
  poke(p);
}

// A return carries the const of the handle too. A function may not hand out a non-const reference through a const handle, decision
// 0038. Its caller would write through it, and the call shows no handle.
int32_t& through_return(const std::unique_ptr<int32_t>& p) {
  return *p;  // BANNED
}

void write_returned(const std::unique_ptr<int32_t>& p) {
  through_return(p) = 42;
}

// A range-for by reference binds each element to a non-const reference, and the range reaches through a const handle. The binding
// is the first write, and the assignment through it the second.
void range_through(const std::unique_ptr<std::array<int32_t, 4>>& p) {
  for (int32_t& x : *p) {  // BANNED
    x = 1;  // BANNED
  }
}

// A pointer stored into an out parameter leaves the handle as a return does, decision 0038.
void hand_out(const std::unique_ptr<int32_t>& p, int32_t*& out) {
  out = p.get();  // BANNED
}

// A capture initializer stores what it takes, as an assignment does. Here it takes a pointer through a const handle, and the lambda
// writes through it, decision 0038.
void capture_out(const std::unique_ptr<int32_t>& p, const std::vector<int32_t>& v) {
  std::ranges::for_each(v, [q = p.get()](int32_t e) { *q = e; });  // BANNED
}

// A brace initializer stores into each member it names. A struct of a system header has a pointer member that no row reads, and the
// pointer leaves the handle through it, decision 0038.
void write_at(int32_t* q) {
  *q = 1;
}

void through_aggregate(const std::unique_ptr<int32_t>& p) {
  iovec v{p.get(), 4};  // BANNED
  write_at(static_cast<int32_t*>(v.iov_base));
}

// A default member initializer stores as a constructor's member initializer does.
struct Holds {
  const std::unique_ptr<int32_t> p;
  int32_t* q = p.get();  // BANNED also: raw_pointer
};

// A const handle gives reads only, decision 0040. A functional cast, an argument by value, an assignment of a class and the brace list
// of a wrapper each carry the pointer out, and none is a read.
iovec made(const std::unique_ptr<int32_t>& p) {
  return iovec{p.get(), 4};  // BANNED
}

void take_iov(iovec v) {
  write_at(static_cast<int32_t*>(v.iov_base));
}

void reassigned(const std::unique_ptr<int32_t>& p, iovec& v) {
  v = iovec{p.get(), 4};  // BANNED
  v = {p.get(), 4};  // BANNED
}

void passed(const std::unique_ptr<int32_t>& p) {
  take_iov(iovec{p.get(), 4});  // BANNED
  take_iov({p.get(), 4});  // BANNED
}

void wrapped(const std::unique_ptr<int32_t>& p) {
  std::optional<iovec> o{iovec{p.get(), 4}};  // BANNED
}

// A const handle that owns a handle or a span. A const method of what it owns can still hand out a way to write, and the walk follows
// it, decision 0040.
void nested(const std::unique_ptr<std::unique_ptr<int32_t>>& p) {
  *p->get() = 1;  // BANNED
}

void owned_span(const std::unique_ptr<std::span<int32_t>>& p) {
  p->subspan(0)[0] = 1;  // BANNED
  p->front() = 1;  // BANNED
}

// A loop variable copied by value is a copy, and a proxy of vector<bool> carries a way to write, decision 0041.
void clear_all(const std::unique_ptr<std::vector<bool>>& p) {
  for (auto bit : *p) {  // BANNED
    bit = false;
  }
}
