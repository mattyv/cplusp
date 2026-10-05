#include <cstddef>
#include <cstdint>
#include <memory>

struct Arena {
  static size_t used;
};

size_t Arena::used = 0;

std::unique_ptr<uint8_t[]> pool;

size_t arena_acquire(size_t size) {
  if (pool == nullptr) {
    pool = std::unique_ptr<uint8_t[]>(new uint8_t[4096]);
  }
  size_t offset = Arena::used;
  Arena::used += size;
  return offset;
}

void arena_release() {
  Arena::used = 0;
}
