#include <cstdint>

// A contract line after code on the same line belongs to nothing, decision 0062. Each is refused, never dropped.
int32_t f1(int32_t x)  //@ ensures result == 7
{
  return x;
}

int32_t f2(int32_t x) {  //@ ensures result == 7
  return x;
}

int32_t f3(int32_t x) { return x; }  //@ ensures result == 7
