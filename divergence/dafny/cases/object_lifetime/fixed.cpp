#include <cstdint>

struct Holder {
  int32_t v = 0;
};

//@ ensures result == 42
int32_t read_later() {
  Holder h;
  {
    int32_t local = 42;
    h.v = local;
  }
  return h.v;
}
