#include <cstdint>
#include <optional>

// Each read of an optional that may be empty is named, decision 0075.
int32_t get(std::optional<int32_t> o) {
  return *o;
}

//@ ensures result.value() >= 0
std::optional<int32_t> nonneg(int32_t x) {
  if (x < 0) {
    return std::nullopt;
  }
  return x;
}

int32_t member(std::optional<int32_t> o) {
  return o.value();
}

std::optional<int32_t> next(int32_t x) {
  return x + 1;
}
