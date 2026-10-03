// The edge where the naive model and the C++ part ways: the vector is at capacity, so push_back moves the elements.
// The pointer p then points into freed memory. The sanitizer reports the read.
#include <cstdint>
#include <cstdio>
#include <vector>

int32_t first_then_grow(std::vector<int32_t>& v);

int main() {
  std::vector<int32_t> v;
  v.reserve(1);
  v.push_back(1);
  std::printf("%d\n", first_then_grow(v));
  return 0;
}
