#include <cstddef>
#include <cstdint>

//@ ensures result == (i < n)
bool below(int32_t i, size_t n) {
  return i < n;
}
