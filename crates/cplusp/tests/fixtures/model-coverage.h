#pragma once
#include <cstdint>

// A function in a project header is in view, so the translator models it.
//@ ensures result == x
inline int32_t in_header(int32_t x) {
  return x;
}
