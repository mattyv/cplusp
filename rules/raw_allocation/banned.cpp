#include <cstdint>
#include <cstdlib>

int32_t* make() {
  return new int32_t(1);  // BANNED
}

void unmake(int32_t* p) {
  delete p;  // BANNED
}

int32_t with_malloc() {
  std::free(std::malloc(sizeof(int32_t)));  // BANNED
  return 0;
}
