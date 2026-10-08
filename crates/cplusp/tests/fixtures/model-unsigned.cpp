#include <cstdint>

// An unsigned literal is outside the subset, decision 0060. C++ wraps -1u, and a model that dropped the type would prove a wrong result.
//@ ensures result == (0 < 1)
bool wrong() {
  return -1u < 1u;
}

bool wrong_sub() {
  return (0u - 1u) < 1u;
}
