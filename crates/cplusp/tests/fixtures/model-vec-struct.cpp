#include <algorithm>
#include <cstdint>
#include <vector>

// A vector of a struct by reference, as a local and as a result, and a vector as a result, decision 0163.
struct Item {
  int32_t key;
  int32_t value;
};

//@ modifies items
//@ ensures items.size() == old(items.size())
//@ ensures forall i, j :: 0 <= i < j < items.size() ==> items[i].key <= items[j].key
void sort_by_key(std::vector<Item>& items) {
  std::sort(items.begin(), items.end(), [](const Item& a, const Item& b) { return a.key < b.key; });
}

//@ ensures result.size() == items.size()
//@ ensures forall i, j :: 0 <= i < j < result.size() ==> result[i].key <= result[j].key
std::vector<Item> sorted_copy(const std::vector<Item>& items) {
  std::vector<Item> sorted = items;
  std::sort(sorted.begin(), sorted.end(), [](const Item& a, const Item& b) { return a.key < b.key; });
  return sorted;
}

//@ requires items.size() >= 2
//@ ensures result
bool caller(const std::vector<Item>& items) {
  std::vector<Item> sorted = sorted_copy(items);
  return sorted[0].key <= sorted[1].key;
}

//@ requires v.size() <= 100
//@ ensures result.size() == v.size() + 1
std::vector<int32_t> appended(const std::vector<int32_t>& v) {
  std::vector<int32_t> out = v;
  out.push_back(0);
  return out;
}
