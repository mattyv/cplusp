#include <cstddef>
#include <utility>
#include <span>
#include <array>
#include <cstdint>
#include <memory>
#include <tuple>
#include <optional>
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

//@ ensures result == (q != nullptr && *q > 0)
bool positive_at(const int32_t* q) {
  return q != nullptr && *q > 0;
}

// A pointer through a const handle may be compared, read through, or handed on as a pointer to const, decision 0040.
//@ requires p != nullptr
//@ ensures result == (*p > 0 ? *p : 0)
int32_t read_by_pointer(const std::unique_ptr<int32_t>& p) {
  if (p.get() == nullptr) {
    return 0;
  }
  return positive_at(p.get()) ? *p.get() : 0;
}

// An explicit conversion to a pointer to const is the conversion the decision lists as a read.
//@ requires p != nullptr
//@ ensures result == (*p > 0)
bool positive_by_cast(const std::unique_ptr<int32_t>& p) {
  return positive_at(static_cast<const int32_t*>(p.get()));
}

// Const reaches the fields of what a const handle owns. A node of unique_ptr members, read through a const reference, carries nothing
// unjudged, decisions 0042 and 0043. So does a const optional of a unique_ptr.
struct Node {
  int32_t value = 0;
  std::unique_ptr<Node> left;
  std::unique_ptr<Node> right;
};

//@ ensures result == n.value
int32_t value_of(const Node& n) {
  return n.value;
}

//@ requires root != nullptr
//@ ensures result == root->value
int32_t root_value(const std::unique_ptr<Node>& root) {
  return value_of(*root);
}

//@ ensures result == o.has_value()
bool present(const std::optional<std::unique_ptr<int32_t>>& o) {
  return o.has_value();
}

//@ requires p != nullptr
//@ ensures result == p->has_value()
bool inner_present(const std::unique_ptr<std::optional<std::unique_ptr<int32_t>>>& p) {
  return present(*p);
}

struct Pairs {
  std::pair<int32_t, int32_t> pr;
  std::tuple<int32_t, int32_t> tp;
  int32_t x = 0;
};

// A copy that carries no way to write is a read of its value, decisions 0040 and 0041, whatever constructor of the library the copy
// takes. In C++23 the library copies a non-const pair through a constructor that takes a non-const reference, and it writes nothing.
//@ requires p != nullptr
//@ ensures result == p->pr.first + std::get<0>(p->tp)
int32_t firsts(const std::unique_ptr<Pairs>& p) {
  std::pair<int32_t, int32_t> c = p->pr;
  std::tuple<int32_t, int32_t> t = p->tp;
  return c.first + std::get<0>(t);
}

//@ requires p != nullptr
//@ ensures result == p->x
int32_t boxed(const std::unique_ptr<Pairs>& p) {
  std::optional<int32_t> o = p->x;
  return o.value_or(0);
}
