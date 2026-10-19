#include <algorithm>
#include <cstdint>
#include <vector>

// A comparator that breaks more than one clause of a strict weak order gives one line, decision 0164.
struct Item {
  int32_t key;
  int32_t value;
};

//@ modifies items
void mixed(std::vector<Item>& items) {
  std::sort(items.begin(), items.end(), [](const Item& a, const Item& b) { return a.key < b.value; });
}
