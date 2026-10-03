#include <cstdint>

//@ requires p != nullptr
int32_t read(const int32_t* p) {
  return *p;
}

int32_t through(int32_t x) {
  return read(&x);
}

struct Holder {
  int32_t v = 0;
};
