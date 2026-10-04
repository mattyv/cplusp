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

int32_t read_fresh() {
  return *(new int32_t{42});  // BANNED
}

void* raw() {
  return ::operator new(4);  // BANNED
}
