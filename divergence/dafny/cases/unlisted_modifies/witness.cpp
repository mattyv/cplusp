// The edge where the naive model and the C++ part ways: add changes total, and its contract does not say so.
// delta() reads total, calls add(1) and reads total again, so it returns 1.
#include <cstdint>
#include <cstdio>

int32_t delta();

int main() {
  std::printf("%d\n", delta());
  return 0;
}
