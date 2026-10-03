#include <cstddef>
#include <cstdint>
#include <vector>

//@ requires x < 0x7FFFFFFF
int32_t next(int32_t& x) {
  return x++;
}

int32_t twice(int32_t a) {
  return 2 * a;
}

bool before(int32_t a, int32_t b) {
  return a < b;
}

struct Counter {
  int32_t n = 0;
  int32_t bump() { return n++; }
  int32_t peek() const { return n; }
};

bool rises(int32_t& x) {
  int32_t first = next(x);
  int32_t second = next(x);
  return before(first, second);
}

bool pure_arguments(int32_t a, int32_t b) {
  return before(twice(a), twice(b));
}

int32_t nested(int32_t& x) {
  return twice(next(x));
}

int32_t one_change(int32_t& x, int32_t a) {
  return next(x) + twice(a);
}

void store(std::vector<int32_t>& v, std::size_t i, int32_t& x) {
  v[i] = next(x);
}

int32_t two_reads(const Counter& c) {
  return c.peek() + c.peek();
}

void append(std::vector<int32_t>& v, int32_t& x) {
  v.push_back(next(x));
}
