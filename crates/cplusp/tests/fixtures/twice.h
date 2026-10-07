#pragma once
#include <cstdint>
#include "../../../../include/cplusp.h"

// One build marks the body trusted and the other does not. Each build judges its own findings.
#ifdef LEGACY
CPLUSP_TRUSTED("the old body, in one build only")
#endif
//@ ensures result == x
inline int32_t body(int32_t x) {
  delete new int32_t(x);
  return x;
}
