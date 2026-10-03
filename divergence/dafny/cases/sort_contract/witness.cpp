// The edge where the model and the C++ agree: std::sort returns a sorted permutation. Prints {3, 1, 2} after the sort.
#include <cstdint>
#include <cstdio>
#include <vector>

void sort_in_place(std::vector<int32_t>& v);

int main() {
  std::vector<int32_t> v = {3, 1, 2};
  sort_in_place(v);
  std::printf("%d %d %d\n", v[0], v[1], v[2]);
  return 0;
}
