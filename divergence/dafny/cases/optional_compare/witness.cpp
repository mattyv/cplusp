// The edge where the naive model and the C++ part ways: the optional is empty.
// An empty optional is not equal to 5, and it is less than 5. Prints the two results.
#include <cstdint>
#include <cstdio>
#include <optional>

bool is_five(const std::optional<int32_t>& o);
bool below_five(const std::optional<int32_t>& o);

int main() {
  std::optional<int32_t> o;
  std::printf("%d %d\n", is_five(o), below_five(o));
  return 0;
}
