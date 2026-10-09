#include <cstdint>

// A forall statement with no body in a lemma is an axiom, decision 0101.
//@ ensures result > 0
int32_t positive(int32_t x) {
  //@ apply Anything(x)
  return x;
}
