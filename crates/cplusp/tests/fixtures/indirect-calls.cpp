#include <cstdint>
#include "../../../../include/cplusp.h"

CPLUSP_PLAIN("an old entry")
//@ ensures true
int32_t legacy(int32_t x);

// A trusted call hands out a pointer. What the call takes does not name the pointer it gives, decision 0049.
CPLUSP_TRUSTED("hands out an entry")
//@ ensures true
auto pick(const int32_t& x) {
  return x > 0 ? &legacy : &legacy;
}

int32_t picked(const int32_t& x) {
  return pick(x)(x);
}

struct Holder {
  int32_t n = 0;
  CPLUSP_TRUSTED("hands out an entry")
  //@ ensures true
  auto table() const {
    return &legacy;
  }
  int32_t run(int32_t x) const {
    return table()(x);
  }
};

// A callable that a trusted body makes calls through what it holds. Its call operator is verified, decision 0047.
CPLUSP_TRUSTED("makes a callable")
//@ ensures true
auto make_callable() {
  struct Callable {
    int32_t (*f)(int32_t);
    int32_t operator()(int32_t x) const {
      return f(x);
    }
  };
  return Callable{&legacy};
}

int32_t called(int32_t x) {
  return make_callable()(x);
}

// A trusted call fills an object that the caller passes. The call can store any pointer in it.
CPLUSP_TRUSTED("makes an empty entry")
//@ ensures true
auto empty_entry() {
  struct Entry {
    int32_t (*f)(int32_t);
  };
  return Entry{nullptr};
}

CPLUSP_TRUSTED("fills an entry")
//@ ensures true
void fill(auto& e) {
  e.f = legacy;
}

int32_t filled(int32_t x) {
  auto e = empty_entry();
  fill(e);
  return e.f(x);
}
