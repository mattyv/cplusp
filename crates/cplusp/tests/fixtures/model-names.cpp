#include <cstdint>

// Names that Dafny reserves, a parameter with no name, and a tab after the word, decision 0057.
//@ ensures	result == old
int32_t keep(int32_t old, int32_t) {
  return old;
}

//@ ensures result == x
int32_t function(int32_t x) {
  return x;
}
