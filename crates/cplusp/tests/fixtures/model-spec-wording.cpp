// An error inside a function of the companion file is named in the words of Dafny, decision 0084.
#include <cstdint>
//@ requires Ok(a)
//@ ensures result == a
int32_t f(int32_t a) { return a; }
