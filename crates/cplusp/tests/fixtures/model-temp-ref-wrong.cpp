#include <cstdint>

// A temporary is the value it is built from, so a claim about another value fails, decision 0181.
struct Pair {
  int32_t a;
  int32_t b;
};

//@ ensures result == p.a
int32_t first(const Pair& p) {
  return p.a;
}

//@ ensures result == 2
int32_t wrong() {
  return first(Pair{1, 2});
}
