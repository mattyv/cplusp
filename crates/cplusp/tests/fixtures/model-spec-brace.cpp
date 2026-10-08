// A companion file that Dafny cannot parse, decision 0083.
#include <cstdint>
//@ requires Ok(a)
//@ ensures result == a
int32_t f(int32_t a) { return a; }
