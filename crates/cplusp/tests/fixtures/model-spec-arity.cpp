// A companion file from the review of 0079, decision 0080.
#include <cstdint>
//@ requires Ok(a, a)
//@ ensures result == a
int32_t f(int32_t a) { return a; }
