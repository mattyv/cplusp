#include <cstdint>

struct Holder {
  const int32_t* p = nullptr;
};

//@ ensures result == 42
int32_t read_later() {
  Holder h;
  {
    int32_t local = 42;
    h.p = &local;
  }
  return *h.p;
}
