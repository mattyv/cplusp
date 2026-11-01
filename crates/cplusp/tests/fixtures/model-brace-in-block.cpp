#include <array>
#include <cstdint>
// A braced list in a bare block gets the sentence of a braced list, decision 0225.

//@ ensures result[0] == 1
std::array<int32_t, 2> two(bool c) {
  {
    return {1};
  }
}
