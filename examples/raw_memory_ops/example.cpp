#include <cstdint>

// A byte copy of a struct is trusted, and its contract says what the destination holds. The body is in trusted.cpp. The caller
// copies into a new local, so the two objects differ, as the contract needs. The prover proves the copy from the contract.
struct Pair {
  int32_t a = 0;
  int32_t b = 0;
};

//@ requires &dst != &src
//@ modifies dst
//@ ensures dst.a == src.a && dst.b == src.b
void copy_pair(Pair& dst, const Pair& src);

//@ ensures result.a == p.a && result.b == p.b
Pair duplicate(const Pair& p) {
  Pair q;
  copy_pair(q, p);
  return q;
}
