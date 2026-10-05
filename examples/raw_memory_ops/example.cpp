#include <cstdint>
#include "../../include/cplusp.h"

// A byte copy of a struct is trusted, and its contract says what the destination holds. The body is in trusted.cpp. The caller copies
// and then swaps the two fields, and the prover proves the result from the contract. The two objects differ, because the gate
// refuses a call that passes one object under two names, row aliasing, decision 0033.
struct Pair {
  int32_t a = 0;
  int32_t b = 0;
};

CPLUSP_TRUSTED("memcpy of a struct of two ints")
//@ modifies dst
//@ ensures dst.a == src.a && dst.b == src.b
void copy_pair(Pair& dst, const Pair& src);

//@ modifies out
//@ ensures out.a == p.b && out.b == p.a
void swapped_copy(Pair& out, const Pair& p) {
  copy_pair(out, p);
  int32_t t = out.a;
  out.a = out.b;
  out.b = t;
}
