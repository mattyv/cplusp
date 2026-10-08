#include <cstdint>

// C++20 wraps a narrowing cast. The model does not, decision 0058: Dafny must prove that the value fits, and here it cannot.
int32_t cut(int64_t x) {
  return static_cast<int32_t>(x);
}
