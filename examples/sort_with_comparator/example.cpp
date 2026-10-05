#include <algorithm>
#include <cstdint>
#include <vector>

// std::sort with a comparator, as a lambda on one field of a struct. The lambda has no capture, and it goes straight to the algorithm.
// Its test is a strict weak order on the key, as std::sort needs, because `<` on the integers is one. The contract is the contract of the
// sort for this comparator: the result is sorted by key, and it holds the same items as the input, as a multiset. It does not say
// that equal keys keep their order, because std::sort does not promise it. example.dfy models the call as the axiom std_sort_by, whose
// postcondition is exactly these two lines. The function sorts a copy, so the vector of the caller stays as it was.
struct Item {
  int32_t key;
  int32_t value;
};

//@ ensures forall i, j :: 0 <= i < j < result.size() ==> result[i].key <= result[j].key
//@ ensures multiset(result) == multiset(items)
std::vector<Item> sorted_by_key(const std::vector<Item>& items) {
  std::vector<Item> sorted = items;
  std::sort(sorted.begin(), sorted.end(), [](const Item& a, const Item& b) { return a.key < b.key; });
  return sorted;
}

// A verified caller. The first item of the sorted copy has the smallest key, and the proof comes from the contract above and nothing else.
//@ requires !items.empty()
//@ ensures forall j :: 0 <= j < items.size() ==> result <= items[j].key
//@ ensures exists j :: 0 <= j < items.size() && items[j].key == result
int32_t smallest_key(const std::vector<Item>& items) {
  std::vector<Item> sorted = sorted_by_key(items);
  return sorted[0].key;
}
