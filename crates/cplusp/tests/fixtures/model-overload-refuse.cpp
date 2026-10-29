#include <cstdint>

// Two virtual functions of one name, decision 0210. A contract cannot call such a function by its name yet.

struct A { int32_t x; };
struct B { int32_t y; };

struct Look {
  virtual ~Look() = default;
  //@ ensures result == a.x
  virtual int32_t see(const A& a) const = 0;
  //@ ensures result == b.y
  virtual int32_t see(const B& b) const = 0;
};

class Eye final : public Look {
 public:
  //@ ensures result == a.x
  int32_t see(const A& a) const override { return a.x; }
  //@ ensures result == b.y
  int32_t see(const B& b) const override { return b.y; }
};

//@ ensures result == a.x + b.y
int64_t both(const Look& l, const A& a, const B& b) {
  return int64_t{l.see(a)} + l.see(b);
}

//@ ensures result == l.see(a)
int32_t see_a(const Look& l, const A& a) {
  return l.see(a);
}
