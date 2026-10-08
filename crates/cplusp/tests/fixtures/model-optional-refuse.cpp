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

// A construction from std::nullopt is None only when it names std::nullopt itself. Any other expression of its type is refused.
//@ ensures true
std::nullopt_t gives_nullopt();

std::optional<int32_t> dropped_call() {
  return gives_nullopt();
}

std::optional<int32_t> dropped_read(std::optional<int32_t> o) {
  return (*o, std::nullopt);
}

std::optional<int64_t> widen(std::optional<int32_t> o) {
  return o;
}
