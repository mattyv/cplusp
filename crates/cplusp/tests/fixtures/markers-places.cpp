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

// Every function keeps its first and last token in one file, a verified one too.
CPLUSP_TRUSTED("builds a helper that ends in another file")
//@ ensures result == x
int32_t local_elsewhere(int32_t x) {
  struct Local {
    int32_t run(int32_t y) {
      delete new int32_t(y);
#include "markers-tail2.inc"
  };
  return Local{}.run(x);
}

// Code in a plain body is plain, a lambda and a local class too.
CPLUSP_PLAIN("old code with helpers")
int legacy_helpers(int x) {
  auto f = [](int y) {
    int* p = new int(y);
    int r = *p;
    delete p;
    return r;
  };
  struct Box {
    int* p = nullptr;
  };
  Box b;
  b.p = new int(f(x));
  int r = *b.p;
  delete b.p;
  return r;
}
