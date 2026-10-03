// The edge where the naive model and the C++ part ways: `*opt` on an empty optional.
// Nothing stops it. The sanitizer does not see it, and the program goes on with a value from nowhere.
#include <cstdint>
#include <cstdio>
#include <optional>

int32_t value(const std::optional<int32_t>& opt);

int main() {
  std::optional<int32_t> opt;
  std::printf("%d\n", opt.has_value());
  int32_t ignored = value(opt);
  (void)ignored;
  std::printf("went on\n");
  return 0;
}
