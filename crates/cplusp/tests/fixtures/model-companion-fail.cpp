#include <cstdint>

// A lemma of the companion file whose proof fails has the sentence of the same failure in the model, decision 0164.
//@ ensures result == x
int32_t same(int32_t x) {
  return x;
}
