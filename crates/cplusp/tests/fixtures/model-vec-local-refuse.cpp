#include <cstdint>
#include <vector>

// A local vector with no rule yet, decision 0160.
//@ modifies v
void fill(std::vector<int32_t>& v) {
}

int32_t empty() {
  std::vector<int32_t> x;
  return 0;
}

int32_t listed() {
  std::vector<int32_t> x = {1, 2, 3};
  return 0;
}

int32_t passed(const std::vector<int32_t>& v) {
  std::vector<int32_t> x = v;
  fill(x);
  return 0;
}
