#include <cstddef>
#include <cstdint>
#include <cstring>

// Trusted: memcpy copies the bytes of a struct of two ints. The gate refuses memcpy on anything but plain bytes, under the
// raw_memory_ops row, which is the point. Verified code sees only the contract in example.cpp.
struct Pair {
  int32_t a = 0;
  int32_t b = 0;
};

void copy_pair(Pair& dst, const Pair& src) {
  std::memcpy(&dst, &src, sizeof(Pair));
}
