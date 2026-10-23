#include <cstdint>
#include "../../../../include/cplusp.h"

// A dropped write, a call too few, and a trusted callee whose requires line the caller does not meet, decision 0173.
int32_t total = 0;

//@ requires -0x40000000 <= x < 0x40000000
//@ requires -0x40000000 <= total < 0x40000000
//@ modifies total
//@ ensures total == old(total) + x
void add(int32_t x) {
  total += x;
  total -= x;
}

//@ requires -0x40000000 <= x < 0x40000000
//@ requires -0x40000000 <= total < 0x40000000
//@ modifies total
//@ ensures total == old(total) + x
void add_right(int32_t x) {
  total += x;
}

//@ requires -0x20000000 <= x < 0x20000000
//@ requires -0x20000000 <= total < 0x20000000
//@ modifies total
//@ ensures total == old(total) + 2 * x
void add_twice(int32_t x) {
  add_right(x);
}

//@ requires total < 1000
//@ modifies total
//@ ensures total == old(total) + 1
CPLUSP_TRUSTED("the count lives in a register of the device")
void tick();

//@ modifies total
//@ ensures total == old(total) + 1
void blind_tick() {
  tick();
}

#include <algorithm>
#include <vector>

int32_t k = 0;

//@ requires v.size() == 1 && v[0] == -5 && k == 5
//@ modifies k
//@ ensures result == 1
int64_t negative_counted_as_positive(const std::vector<int32_t>& v) {
  k += 1;
  int64_t n = std::count_if(v.begin(), v.end(), [](int32_t k) { return k > 0; });
  return n;
}

struct Item {
  int32_t key;
  int32_t value;
};

int32_t g = 0;

//@ requires g == 0 && items.size() == 2 && items[0].key == 1 && items[0].value == 9 && items[1].key == 2 && items[1].value == 3
//@ modifies g, items
//@ ensures items.size() == 2 && items[0].value <= items[1].value
void by_global(std::vector<Item>& items) {
  g += 1;
  std::sort(items.begin(), items.end(), [](const Item& a, const Item& b) { return g > 0 ? a.key < b.key : a.value < b.value; });
}
