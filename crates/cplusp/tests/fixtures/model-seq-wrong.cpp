#include <cstdint>
#include <vector>

// C++ reads out of range with undefined behaviour. The model reads only in range, decision 0064, so this fails in Dafny.
int32_t first(const std::vector<int32_t>& v) {
  return v[0];
}
