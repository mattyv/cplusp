#include <cstdint>
#include "model-coverage.h"

// Each function in view is modelled or refused, and each contract line belongs to a function or is refused, decision 0057.
//@ ensures result == x
template <typename T>
T tmpl(T x) {
  return x;
}

//@ ensures result == x
int32_t abbreviated(auto x) {
  return x;
}

//@ ensures result == 7

int32_t apart(int32_t x) {
  return x;
}

//@ ensures result == 7
// a note between them
int32_t noted(int32_t x) {
  return x;
}

//@ ensures result == x \
&& x == 7
int32_t continued(int32_t x) {
  return x;
}

//@ ensures result <== x
int32_t arrow(int32_t x) {
  return x;
}

// A deleted function runs nothing, so it has no model and no refusal.
int32_t gone(int32_t x) = delete;
