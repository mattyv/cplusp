#include <cstdint>

//@ ensures result == *p
int32_t read(const int32_t* p) {
  return *p;
}
