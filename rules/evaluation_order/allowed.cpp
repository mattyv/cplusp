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

// Beside the one change, a literal or a different local. Neither can see the change.
int32_t one_change(int32_t& x, int32_t a) {
  return next(x) + a;
}

bool change_beside_a_literal(int32_t& x) {
  return before(next(x), 1);
}

bool change_beside_another_local(int32_t& x, int32_t y) {
  return before(next(x), y);
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

int32_t either(bool c, int32_t& x) {
  return c ? next(x) : next(x);
}

bool in_order(int32_t& x, int32_t& y) {
  return before(0, next(x)) && before(0, next(y));
}

#include <utility>

void sink(std::vector<int32_t> a, std::vector<int32_t> b);

void moved(std::vector<int32_t>& a, std::vector<int32_t>& b) {
  sink(std::move(a), std::move(b));
}

int32_t ends(std::vector<int32_t>& v) {
  return v.front() + v.back();
}

int32_t two_at(std::vector<int32_t>& v) {
  return v.at(0) + v.at(1);
}

int32_t unevaluated(int32_t& x) {
  return static_cast<int32_t>(sizeof(next(x))) + next(x);
}

#include <tuple>

void take(std::pair<int32_t, int32_t> p, std::pair<int32_t, int32_t> q);

void paired(int32_t a, int32_t b, int32_t c, int32_t d) {
  take(std::make_pair(a, b), std::make_pair(c, d));
}

int32_t both_of(std::tuple<int32_t, int32_t>& t) {
  return std::get<0>(t) + std::get<1>(t);
}
