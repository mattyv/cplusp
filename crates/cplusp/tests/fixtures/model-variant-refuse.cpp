#include <array>
#include <cstdint>
#include <variant>
#include <vector>

// What a variant has no rule for yet, decision 0202.
//@ ensures true
bool three(const std::variant<int32_t, bool, uint64_t>& v) {
  return std::holds_alternative<bool>(v);
}

//@ ensures result == std::holds_alternative<int64_t>(v)
bool other(const std::variant<int32_t, bool>& v) {
  return std::holds_alternative<bool>(v);
}

//@ ensures true
bool second(const std::variant<int32_t, bool>& v) {
  return v.index() == 1;
}

// An alternative that can leave the variant with no value, decision 0206.
struct Bag {
  std::vector<int32_t> xs;
};

struct Big {
  std::array<int32_t, 100> a;
};

//@ ensures true
bool bag(const std::variant<Bag, uint64_t>& v) {
  return std::holds_alternative<uint64_t>(v);
}

//@ ensures true
bool big(const std::variant<Big, uint64_t>& v) {
  return std::holds_alternative<uint64_t>(v);
}

// An order of two variants, and a variant of one type twice, decision 0206.
//@ requires v < w
bool order(const std::variant<int32_t, bool>& v, const std::variant<int32_t, bool>& w) {
  return std::holds_alternative<bool>(v);
}

//@ ensures true
bool twice(const std::variant<int32_t, int32_t>& v) {
  return true;
}
