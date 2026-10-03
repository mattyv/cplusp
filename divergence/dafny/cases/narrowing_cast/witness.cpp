// The edge where the naive model and the C++ part ways: 200 does not fit in int8_t. C++20 defines the result.
#include <cstdint>
#include <cstdio>

int8_t narrow(int32_t x);

int main() {
  std::printf("%d\n", narrow(200));
  return 0;
}
