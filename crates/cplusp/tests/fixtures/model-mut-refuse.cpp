#include <cstdint>

// Writes with no rule yet are refused at their lines, decision 0096.
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
