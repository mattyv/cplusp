#include <cstdint>

//@ requires x < 0x7FFFFFFF
int32_t next(int32_t& x) {
  return x++;
}

bool before(int32_t a, int32_t b) {
  return a < b;
}

struct Counter {
  int32_t n = 0;
  int32_t bump() { return n++; }
};

bool rises(int32_t& x) {
  return before(next(x), next(x));  // BANNED
}

int32_t both(int32_t& x, int32_t& y) {
  return next(x) + next(y);  // BANNED
}

int32_t twice_bumped(Counter& c) {
  return c.bump() + c.bump();  // BANNED
}

int32_t unsequenced(int32_t& x) {
  return x++ - x++;  // BANNED
}

#include <utility>

bool mixed(int32_t& x) {
  return before(next(x), x++);  // BANNED
}

int32_t twice(int32_t a) {
  return 2 * a;
}

int32_t total = 0;

// One change and a read of what it changes. Clang says true, GCC says false.
bool change_and_read(int32_t& x) {
  return before(next(x), x);  // BANNED
}

// One change beside a call. Any call may read the State the change may write.
int32_t change_beside_a_call(int32_t& x, int32_t a) {
  return next(x) + twice(a);  // BANNED
}

// One change beside a global, which is the State.
int32_t change_beside_a_global(int32_t& x) {
  return next(x) + total;  // BANNED also: global_state
}

// A non-const call on an object beside a member of that object.
int32_t object_and_member(Counter& c) {
  return c.bump() + c.n;  // BANNED
}

bool exchanged(int32_t& x) {
  return before(std::exchange(x, 1), std::exchange(x, 2));  // BANNED
}

#include <random>
#include <span>

struct Taker {
  explicit Taker(int32_t& x) { x++; }
};

void take2(Taker a, Taker b);

void both_constructed(int32_t& x) {
  take2(Taker(x), Taker(x));  // BANNED
}

uint32_t two_draws(std::mt19937& g) {
  return g() + g();  // BANNED
}

struct Writer {
  int32_t bump(int32_t& x) const { return x++; }
};

int32_t const_method_writes(const Writer& w, int32_t& x) {
  return w.bump(x) + w.bump(x);  // BANNED
}

int32_t at(int32_t& x) {
  return x++;
}

bool shadowed_name(int32_t& x) {
  return before(at(x), at(x));  // BANNED
}

int32_t write(std::span<int32_t> s) {
  return s[0]++;
}

bool through_span(std::span<int32_t> s) {
  return before(write(s), write(s));  // BANNED
}

bool before_total(int32_t a, int32_t b = total);

// The default argument reads the global beside the change.
bool read_by_default(int32_t& x) {
  return before_total(next(x));  // BANNED also: global_state
}

// A capture initializer reads x beside the change of x.
int32_t captured_beside(int32_t& x) {
  return std::make_pair(next(x), [k = x] { return k; }).first;  // BANNED
}

// A capture initializer that changes state is a change of state, beside the other one.
int32_t captured_change(int32_t& x) {
  return std::make_pair(next(x), [k = next(x)] { return k; }).first;  // BANNED
}
