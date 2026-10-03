#include <cstddef>
#include <cstdint>

//@ ensures result == (i < n)
bool below(int32_t i, size_t n) {
  return i < 0 || static_cast<size_t>(i) < n;
}
