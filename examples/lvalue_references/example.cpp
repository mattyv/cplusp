#include <cstdint>

// A reference is an alias, so two references may name one object. This function moves the value of src into dst and clears src.
// For take(x, x) the second line clears the value that the first line copied, so the contract is false for that call. The
// requires line keeps the two apart, and the prover checks the body for that case only.
//@ requires &dst != &src
//@ modifies dst, src
//@ ensures dst == old(src) && src == 0
void take(int32_t& dst, int32_t& src) {
  dst = src;
  src = 0;
}
