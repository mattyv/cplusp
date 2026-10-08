// A companion file from the second review of the companion check, decision 0083.
#include <cstdint>
//@ requires Ok(a)
//@ ensures result == a + 1
int32_t f(int32_t a) { return a; }
