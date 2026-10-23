#include <cstdint>
#include "../../../../include/cplusp.h"

// A global that a function lists is an implicit parameter of it, decision 0173. A modifies line makes it a reference parameter,
// and a reads line a parameter by value. A static data member has its qualified name.
int32_t total = 0;

//@ requires -0x40000000 <= x < 0x40000000
//@ requires -0x40000000 <= total < 0x40000000
//@ modifies total
//@ ensures total == old(total) + x
void add(int32_t x) {
  total += x;
}

//@ reads total
//@ ensures result == total
int32_t current() {
  return total;
}

//@ requires -0x20000000 <= x < 0x20000000
//@ requires -0x20000000 <= total < 0x20000000
//@ modifies total
//@ ensures total == old(total) + 2 * x
void add_twice(int32_t x) {
  add(x);
  add(x);
}

struct Registry {
  static int32_t last_id;
};

int32_t Registry::last_id = 0;

//@ requires Registry::last_id < 0x7FFFFFFF
//@ modifies Registry::last_id
//@ ensures Registry::last_id == old(Registry::last_id) + 1
//@ ensures result == Registry::last_id
int32_t next_id() {
  Registry::last_id += 1;
  return Registry::last_id;
}

int32_t a = 0;
int32_t b = 0;

//@ requires a < 1000
//@ modifies a
//@ ensures a == old(a) + 1
void inc_a() {
  a += 1;
}

//@ requires b < 1000
//@ modifies b
//@ ensures b == old(b) + 1
void inc_b() {
  b += 1;
}

// inc_a cannot change b, so the second line holds with no frame line.
//@ requires a < 1000 && b < 1000
//@ modifies a, b
//@ ensures a == old(a) + 1 && b == old(b) + 1
void both() {
  inc_a();
  inc_b();
}

//@ requires -0x40000000 <= r < 0x40000000 && -0x40000000 <= total < 0x40000000
//@ modifies r, total
//@ ensures r == old(r) + old(total) && total == old(total) + 1
void add_to(int32_t& r) {
  r += total;
  total += 1;
}

//@ requires 0 <= total < 1000
//@ modifies total
//@ ensures result == old(total) && total == old(total) + 1
int32_t take() {
  int32_t x = 0;
  add_to(x);
  return x;
}

//@ requires total < 1000
//@ modifies total
//@ ensures total == old(total) + 1
CPLUSP_TRUSTED("the count lives in a register of the device")
void tick();

//@ requires total < 999
//@ modifies total
//@ ensures total == old(total) + 2
void two_ticks() {
  tick();
  tick();
}

#include <algorithm>
#include <vector>

int32_t k = 0;

// The parameter k of the lambda hides the global k inside the lambda, as in C++.
//@ requires v.size() == 1 && v[0] == -5 && k == 5
//@ modifies k
//@ ensures result == 0
int64_t positives(const std::vector<int32_t>& v) {
  k += 1;
  int64_t n = std::count_if(v.begin(), v.end(), [](int32_t k) { return k > 0; });
  return n;
}

struct Item {
  int32_t key;
  int32_t value;
};

int32_t g = 0;

// The comparator reads the global after the write, so the sort is by key.
//@ requires g == 0 && items.size() == 2 && items[0].key == 1 && items[0].value == 9 && items[1].key == 2 && items[1].value == 3
//@ modifies g, items
//@ ensures items.size() == 2 && items[0].key <= items[1].key
void by_global(std::vector<Item>& items) {
  g += 1;
  std::sort(items.begin(), items.end(), [](const Item& a, const Item& b) { return g > 0 ? a.key < b.key : a.value < b.value; });
}
