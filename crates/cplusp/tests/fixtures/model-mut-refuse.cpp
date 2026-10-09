#include <cstdint>
#include <optional>
// Writes and calls with no rule yet are refused at their lines, decisions 0096 and 0097.
struct Counter {
  int32_t n_;

  void bump() {
    n_ += 1;
  }
};

struct Pair {
  Counter c_;
};

int32_t on_param(Counter c) {
  c.bump();
  return 0;
}

int32_t on_field(Pair p) {
  Pair q = p;
  q.c_.bump();
  return 0;
}

//@ ensures result == old(x)
int32_t old_outside(int32_t x) {
  return x;
}

void nothing() {
  return;
}

void ret_void() {
  return nothing();
}

int32_t one() {
  return 1;
}

int32_t drops() {
  one();
  return 0;
}

struct Maybe {
  std::optional<int32_t> o_;

  void set() {
    o_ = 1;
  }
};
