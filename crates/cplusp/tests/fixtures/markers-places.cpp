#include <cstdint>
#include "../../../../include/cplusp.h"

// A local class in a trusted body is a function of its own, with no marker, so it is verified.
CPLUSP_TRUSTED("builds a local helper")
//@ ensures result == x
int32_t local_class(int32_t x) {
  struct Local {
    int32_t run(int32_t y) {
      delete new int32_t(y);
      return y;
    }
  };
  return Local{}.run(x);
}

// So is a lambda in a trusted body.
CPLUSP_TRUSTED("calls a helper lambda")
//@ ensures result == x
int32_t lambda_inside(int32_t x) {
  auto f = [](int32_t y) {
    delete new int32_t(y);
    return y;
  };
  return f(x);
}

// An explicit specialization takes only the markers written on it.
//@ ensures result == x
template <typename T>
CPLUSP_TRUSTED("a generic echo")
T echo(T x) {
  return x;
}

template <>
int32_t echo<int32_t>(int32_t x) {
  delete new int32_t(x);
  return x;
}

// A marked function keeps its first and last token in its own file, outside a macro.
#define END } int32_t hidden(int32_t x) { delete new int32_t(x); return x; }
CPLUSP_TRUSTED("ends in a macro")
//@ ensures result == x
int32_t ends_in_macro(int32_t x) {
  delete new int32_t(x);
  return x;
END

CPLUSP_TRUSTED("ends in another file")
//@ ensures result == x
int32_t ends_elsewhere(int32_t x) {
  delete new int32_t(x);
#include "markers-tail.inc"
