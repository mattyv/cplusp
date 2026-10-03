#include <cstdint>
const int32_t& first() {
  int32_t local = 1;
  return local;  // BANNED
}

int32_t* address() {
  int32_t local = 1;
  return &local;  // BANNED
}
