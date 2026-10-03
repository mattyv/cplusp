#include <cstdint>
#include <new>

void construct_in(void* where, int32_t v) {
  new (where) int32_t(v);  // BANNED
}

int32_t read_back(int32_t* p) {
  return *std::launder(p);  // BANNED
}
