#include <cstdlib>

int make_and_read() {
  int* p = new int(1);  // BANNED
  const int v = *p;
  delete p;  // BANNED
  return v;
}

int with_malloc() {
  void* raw = std::malloc(sizeof(int));  // BANNED
  std::free(raw);  // BANNED
  return 0;
}
