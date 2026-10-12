#include <cstdint>
#include <optional>
#include <vector>

// An optional of a struct that holds a sequence stays out, decision 0137, as a struct that holds one is a parameter only, decision 0076.
struct Bag {
  std::vector<int32_t> items;
};

//@ ensures result.has_value()
std::optional<Bag> wrap(const Bag& b) {
  return b;
}
