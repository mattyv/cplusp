#include <cstdint>
#include <iterator>
#include <vector>

int64_t first_two(const std::vector<int64_t>& values) {
  auto it = values.begin();  // BANNED
  int64_t a = *it;
  ++it;
  int64_t b = *it;
  return a + b;
}

int64_t third(const std::vector<int64_t>& values) {
  return *std::next(values.begin(), 2);  // BANNED
}

bool has_negative(const std::vector<int64_t>& values) {
  for (std::vector<int64_t>::const_iterator it = values.begin(); it != values.end(); ++it) {  // BANNED
    if (*it < 0) {
      return true;
    }
  }
  return false;
}

int32_t grow_in_loop(std::vector<int32_t>& v) {
  int32_t s = 0;
  for (const int32_t x : v) {  // BANNED
    s += x;
    v.push_back(x);
  }
  return s;
}

void grow(std::vector<int32_t>& v, int32_t x);

int32_t grow_through_call(std::vector<int32_t>& v) {
  int32_t s = 0;
  for (const int32_t x : v) {  // BANNED
    s += x;
    grow(v, x);
  }
  return s;
}

int32_t grow_in_parentheses(std::vector<int32_t>& v) {
  int32_t s = 0;
  for (const int32_t x : (v)) {  // BANNED
    s += x;
    v.push_back(x);
  }
  return s;
}

struct Bag {
  std::vector<int32_t> items;
  void double_up() {
    for (const int32_t x : items) {  // BANNED
      items.push_back(x);
    }
  }
};

#include <utility>

struct Pile {
  std::vector<int32_t> items;
  void grow() { items.push_back(1); }
  void loop() {
    for (const int32_t x : items) {  // BANNED
      grow();
    }
  }
};

void replace_in_loop(std::vector<int32_t>& v, const std::vector<int32_t>& w) {
  for (const int32_t x : v) {  // BANNED
    v = w;
  }
}

int32_t grow_const_view(std::vector<int32_t>& v) {
  int32_t s = 0;
  for (const int32_t x : std::as_const(v)) {  // BANNED
    s += x;
    v.push_back(x);
  }
  return s;
}
