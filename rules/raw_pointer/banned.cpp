#include <cstdint>

struct Holder {
  const int32_t* p = nullptr;  // BANNED
};

int32_t read_later(int32_t x) {
  const int32_t* q = &x;  // BANNED
  return *q;
}
