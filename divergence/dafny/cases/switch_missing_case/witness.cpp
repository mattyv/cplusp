// The edge where the naive model and the C++ part ways: Slow has no case.
// No case matches and there is no default, so the switch does nothing and the function returns 0.
#include <cstdint>
#include <cstdio>

enum class Mode : uint8_t { Fast, Slow };

int32_t pick(Mode m);

int main() {
  std::printf("%d\n", pick(Mode::Slow));
  return 0;
}
