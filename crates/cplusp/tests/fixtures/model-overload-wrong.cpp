#include <cstdint>

// Two virtual functions of one name, decision 0210. An override that breaks the promise fails its check.

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
  //@ ensures result == b.y + 1
  int32_t see(const B& b) const override { return b.y + 1; }
};

//@ ensures result == a.x + b.y
int64_t both(const Look& l, const A& a, const B& b) {
  return int64_t{l.see(a)} + l.see(b);
}
