#include <cstdint>

// A reference is an alias, so two references may name one object. The contract says they do not, and the prover
// checks the body for that case. Without the requires line the contract would be false for swap_values(x, x).
//@ requires &a != &b
//@ modifies a, b
//@ ensures a == old(b) && b == old(a)
void swap_values(int32_t& a, int32_t& b) {
  int32_t t = a;
  a = b;
  b = t;
}
