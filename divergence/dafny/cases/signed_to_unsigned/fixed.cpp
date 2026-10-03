#include <cstddef>
#include <cstdint>

//@ requires i >= 0
//@ ensures result == i
std::size_t index_of(int32_t i) {
  return static_cast<std::size_t>(i);
}
