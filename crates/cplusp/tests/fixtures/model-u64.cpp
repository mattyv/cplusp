#include <cstdint>

// A literal over the full range of uint64_t, in code and in a contract, decision 0063.
//@ ensures result == 18446744073709551615
uint64_t top() {
  return 18446744073709551615ULL;
}
