// The edge where the naive model and the C++ part ways: 7 is a valid value of Mode, and it has no enumerator.
#include <cstdint>
#include <cstdio>

enum class Mode : uint8_t { Fast, Slow };

Mode to_mode(uint8_t v);

int main() {
  std::printf("%d\n", static_cast<uint8_t>(to_mode(7)));
  return 0;
}
