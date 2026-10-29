#include <cstdint>
#include <optional>

// A field of a base with data has no rule through the class, in a write and in a read, decision 0203.
struct P {
  int32_t x;
};

struct Q : P {
  int32_t x;
  //@ ensures true
  void set() { P::x = 3; }
  //@ ensures true
  void bump() { P::x += 1; }
};

struct R : P {
  int32_t y;
  //@ ensures true
  void put() { x = 3; }
};

//@ modifies q
//@ ensures true
void via_ref(Q& q) {
  q.P::x = 3;
}

//@ ensures true
int32_t via_ptr(const Q* q) {
  if (q == nullptr) {
    return 0;
  }
  return q->P::x;
}

//@ ensures true
int32_t via_opt() {
  std::optional<R> o = R{{1}, 2};
  return o->x;
}

//@ modifies p
//@ ensures true
void set_p(P& p) {
  p.x = 1;
}

//@ modifies r
//@ ensures true
void pass_on(R& r) {
  set_p(r);
}

namespace ns {
struct P2 {
  int32_t z;
};
struct Q2 : P2 {
  int32_t w;
};
}  // namespace ns

//@ ensures true
int32_t named(const ns::Q2& q) {
  return q.z;
}
