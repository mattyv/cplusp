#include <cstdint>
#include <cstdlib>

int32_t make_and_read() {
  int32_t* p = new int32_t(1);  // BANNED
  const int32_t v = *p;
  delete p;  // BANNED
  return v;
}

int32_t with_malloc() {
  void* raw = std::malloc(sizeof(int32_t));  // BANNED
  std::free(raw);  // BANNED
  return 0;
}
