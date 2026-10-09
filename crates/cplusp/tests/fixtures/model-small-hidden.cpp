#include <cstdint>

// A static member and a namespace constant hide a constant of the file with the same name, decision 0107.
constexpr int32_t kScale = 10;
constexpr int32_t k = 10;

struct Fixed {
  static constexpr int32_t kScale = 3;
  int32_t n;
  //@ ensures result == kScale
  int32_t get() const {
    return 10;
  }
};

namespace ns {
constexpr int32_t k = 3;
//@ ensures result == k
int32_t get() {
  return 10;
}
}
