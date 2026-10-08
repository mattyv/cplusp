#include <cstdint>
#include <optional>

// An optional scalar is a Dafny Option, decision 0075.
//@ ensures x < 0 ==> !result.has_value()
//@ ensures x >= 0 ==> result.has_value() && result.value() == x
std::optional<int32_t> nonneg(int32_t x) {
  if (x < 0) {
    return std::nullopt;
  }
  return x;
}

//@ requires o.has_value()
//@ ensures result == o.value()
int32_t get(std::optional<int32_t> o) {
  return *o;
}

//@ requires o.has_value() && o.value() > 0
//@ ensures result > 0
int32_t positive(const std::optional<int32_t>& o) {
  return o.value();
}

struct Slot {
  std::optional<int32_t> value;
};

//@ ensures result == s.value.has_value()
bool full(const Slot& s) {
  return s.value.has_value();
}

//@ ensures result == o
std::optional<int32_t> pass(std::optional<int32_t> o) {
  std::optional<int32_t> r = o;
  return r;
}

//@ ensures !result.has_value()
std::optional<int32_t> none() {
  std::optional<int32_t> r = std::nullopt;
  return r;
}

//@ ensures result.has_value() && result.value() == 7
std::optional<int32_t> seven() {
  return nonneg(7);
}
