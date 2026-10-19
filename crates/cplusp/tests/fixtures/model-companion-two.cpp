#include <cstdint>

// Two clauses of a companion lemma that fail are two lines, each with the line of the companion file that it breaks, decision
// 0164.
//@ ensures result == x
int32_t needs(int32_t x) {
  //@ apply Needs(x)
  return x;
}
