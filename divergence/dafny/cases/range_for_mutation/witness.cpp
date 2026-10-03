// The edge where the naive model and the C++ part ways: the vector has no spare capacity, so push_back moves the elements.
// The range-for holds iterators into the old storage. The sanitizer reports the read through them.
#include <cstdint>
#include <cstdio>
#include <vector>

int32_t sum_and_double(std::vector<int32_t>& v);

int main() {
  std::vector<int32_t> v = {1, 2, 3};
  std::printf("%d\n", sum_and_double(v));
  return 0;
}
