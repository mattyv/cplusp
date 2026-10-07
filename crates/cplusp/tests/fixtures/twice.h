#pragma once
#include <cstdint>
#include "../../../../include/cplusp.h"

// One build marks the body plain and the other does not. Each build judges its own findings.
#ifdef LEGACY
CPLUSP_PLAIN("the old body, in one build only")
#endif
inline int32_t body(int32_t x) {
  delete new int32_t(x);
  return x;
}
