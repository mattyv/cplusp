#include <cstddef>
#include <cstdint>

//@ ensures result == a[i]
int32_t at(const int32_t (&a)[4], size_t i) {
  return a[i];
}
