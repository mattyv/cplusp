#include <bit>
#include <cstdint>

// The standard library has a name for what the builtin does, and the name has a contract.
//@ ensures result <= 32
int32_t ones(uint32_t x) {
  return std::popcount(x);
}
