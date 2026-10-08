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

// An unnamed parameter beside one that the author calls _0: two names, decision 0058. The placeholder is one that C++ cannot write.
//@ ensures result == _0
int32_t unnamed(int32_t, int32_t _0) {
  return _0;
}
