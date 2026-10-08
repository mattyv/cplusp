#include <cstdint>

// A literal keeps its type, decision 0060, and the model never wraps, decision 0061. C++ wraps -1u, and a model that dropped the type
// would prove a wrong result.
//@ ensures result == (0 < 1)
bool wrong() {
  return -1u < 1u;
}

bool wrong_sub() {
  return (0u - 1u) < 1u;
}
