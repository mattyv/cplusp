#include <cstdint>
#include <optional>

// Uses of an optional with no rule are refused at their lines, decision 0075.
int32_t as_bool(std::optional<int32_t> o) {
  if (o) {
    return 1;
  }
  return 0;
}

std::optional<int32_t> write(int32_t x) {
  std::optional<int32_t> r = std::nullopt;
  r = x;
  return r;
}

bool compare(std::optional<int32_t> a, std::optional<int32_t> b) {
  return a == b;
}

struct Point {
  int32_t x;
};

int32_t of_struct(std::optional<Point> p) {
  return 0;
}
