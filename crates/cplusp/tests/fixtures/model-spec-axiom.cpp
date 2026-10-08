#include <cstdint>

// A companion file with an axiom: Max has no body and an ensures line, decision 0079. Dafny proves this function from it, so the
// run must not say proved.
//@ ensures result == Max(a, b)
int32_t larger(int32_t a, int32_t b) {
  return a;
}
