#include <new>

void construct_in(void* where, int v) {
  new (where) int(v);  // BANNED
}

int read_back(int* p) {
  return *std::launder(p);  // BANNED
}
