#include <algorithm>
#include <cstdint>
#include <vector>

int32_t square(int32_t x) {
  return x * x;
}

int32_t apply_square(int32_t x) {
  return square(x);
}

// A lambda passed straight to a std call is a direct call in the code the compiler makes, decision 0050.
void sort_by_lambda(std::vector<int32_t>& v) {
  std::sort(v.begin(), v.end(), [](int32_t a, int32_t b) { return a < b; });
}
