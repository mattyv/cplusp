#include <cstdint>

// Assert and apply lines with no rule are refused at their lines, decision 0099.
int32_t no_result(int32_t x) {
  //@ assert result == x
  return x;
}

int32_t no_lemma(int32_t x) {
  //@ apply Missing(x)
  return x;
}

int32_t at_end(int32_t x) {
  int32_t y = x;
  return y;
  //@ assert y == x
}

int32_t not_a_lemma(int32_t x) {
  //@ apply Double(x)
  return x;
}
