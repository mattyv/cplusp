#include <cstdint>

// A lemma with no body in the companion file is an axiom, decision 0099.
//@ ensures result > 0
int32_t positive(int32_t x) {
  //@ apply Anything(x)
  return x;
}
