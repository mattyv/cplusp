#include <cstdint>
#include "../../../../include/cplusp.h"

// A reference parameter on the modifies line takes a value in and gives it back, decision 0108.
struct Pair {
  int32_t a = 0;
  int32_t b = 0;
};

//@ modifies dst, src
//@ ensures dst == old(src) && src == 0
void take(int32_t& dst, int32_t& src) {
  dst = src;
  src = 0;
}

//@ ensures result == 5
int32_t use_take() {
  int32_t a = 1;
  int32_t b = 5;
  take(a, b);
  return a;
}

//@ requires x < 1000
//@ modifies x
//@ ensures x == old(x) + 1
void bump(int32_t& x) {
  x += 1;
}

//@ requires x < 500
//@ modifies x
//@ ensures x == old(x) + 2
void bump_twice(int32_t& x) {
  bump(x);
  ++x;
}

//@ requires x < 0x7FFFFFFF
//@ modifies x
//@ ensures x == old(x) + 1
//@ ensures result == old(x)
int32_t next(int32_t& x) {
  int32_t before = x;
  x = x + 1;
  return before;
}

//@ requires 0 <= x && x < 0x3FFFFFFF
//@ modifies x
//@ ensures x == old(x) + 2
//@ ensures result == 2 * old(x) + 1
int32_t two_steps(int32_t& x) {
  int32_t first = next(x);
  int32_t second = next(x);
  return first + second;
}

//@ requires out.a < 1000
//@ modifies out
//@ ensures out.a == old(out.a) + 1 && out.b == old(out.b)
void bump_field(Pair& out) {
  out.a += 1;
}

//@ modifies out
//@ ensures out.a == p.b && out.b == p.a
void swapped(Pair& out, const Pair& p) {
  out = p;
  int32_t t = out.a;
  out.a = out.b;
  out.b = t;
}

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
