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

void take2(Taker a, Taker b) {}

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

// A read beside a change inside a template, judged at its instantiation, decision 0036. Clang says true, GCC says false.
template <class T>
bool before_in_template(T& x) {
  return before(next(x), x);  // BANNED
}

bool use_before_in_template(int32_t& x) {
  return before_in_template(x);
}

//@ requires total < 0x7FFFFFFF
//@ modifies total
int32_t next_total() {
  total += 1;
  return total;
}

// 2. A call that changes a global is a change of state, though it has no mutable parameter. Clang says true, GCC false.
//@ requires total < 0x7FFFFFFF
//@ modifies total
bool global_beside() {
  return before(next_total(), total);  // BANNED
}

//@ requires total < 0x7FFFFFFE
//@ modifies total
int32_t two_global_changes() {
  return next_total() + next_total();  // BANNED
}

int32_t opaque();

// A callee with no body here and no contract lines may change anything, so two calls of it are two changes.
int32_t opaque_twice() {
  return opaque() + opaque();  // BANNED also: global_state
}

#include <algorithm>
#include <vector>

bool any_and(bool a, bool b) {
  return a && b;
}

// A lambda inside a std call runs inside the call, so the call changes what the lambda changes, decision 0037. Two such calls
// are two changes.
//@ requires total < 0x7FFFFFFE
//@ modifies total
bool two_lambdas(const std::vector<int32_t>& v) {
  return any_and(std::ranges::any_of(v, [](int32_t x) { total += 1; return x > 0; }), std::ranges::any_of(v, [](int32_t x) { total += 1; return x < 0; }));  // BANNED
}

struct Vec1 {
  int32_t x = 0;
};

//@ requires total < 0x7FFFFFFF
//@ modifies total
Vec1 operator+(Vec1 a, Vec1 b) {
  total += 1;
  return Vec1{a.x + b.x};
}

int32_t sum_x(Vec1 a, Vec1 b) {
  return a.x + b.x;
}

// An operator call is a call, judged by its callee's lines like any other, decision 0037.
//@ requires total < 0x7FFFFFFE
//@ modifies total
int32_t two_sums(Vec1 a, Vec1 b, Vec1 c, Vec1 d) {
  return sum_x(a + b, c + d);  // BANNED
}

struct Noted {
  int32_t v = 0;
  Noted() = default;
  //@ requires total < 0x7FFFFFFF
  //@ modifies total
  Noted(const Noted& other) : v(other.v) {
    total += 1;
  }
};

bool both_empty(std::vector<Noted> a, std::vector<Noted> b) {
  return a.empty() && b.empty();
}

// Two copies of a container of Noted. Each copy runs Noted's copy constructor, which lists total. Two changes, decision 0037.
//@ requires total < 0x7FFFFFFE
//@ modifies total
bool copied_twice(const std::vector<Noted>& v) {
  return both_empty(v, v);  // BANNED
}

#include <variant>

struct Counter2 {
  //@ requires total < 0x7FFFFFFF
  //@ modifies total
  int32_t operator()(const int32_t&, const int32_t&) const { return total += 1; }
  //@ requires total < 0x7FFFFFFF
  //@ modifies total
  int32_t operator()(const int32_t&, const bool&) const { return total += 1; }
  //@ requires total < 0x7FFFFFFF
  //@ modifies total
  int32_t operator()(const bool&, const int32_t&) const { return total += 1; }
  //@ requires total < 0x7FFFFFFF
  //@ modifies total
  int32_t operator()(const bool&, const bool&) const { return total += 1; }
};

int32_t add2(int32_t a, int32_t b) {
  return a + b;
}

// Two visits over two variants each. The library calls the visitor through a table of function pointers, and each visit changes total,
// decision 0037.
//@ requires total < 0x7FFFFFFE
//@ modifies total
int32_t two_visits(const std::variant<int32_t, bool>& x, const std::variant<int32_t, bool>& y) {
  return add2(std::visit(Counter2{}, x, y), std::visit(Counter2{}, x, y));  // BANNED
}

// make_pair copies its argument, and the copy runs Noted's copy constructor, which changes total. Beside it, a read of total,
// decision 0038.
//@ requires total < 0x7FFFFFFF
//@ modifies total
bool pair_beside_a_read(const Noted& n) {
  return before(std::make_pair(n, int32_t{0}).second, total);  // BANNED
}

//@ requires total < 0x7FFFFFFF
//@ modifies total
int32_t take_next() {
  return total += 1;
}

struct Ticket {
  int32_t n = take_next();
};

bool ticket_first(Ticket t, int32_t b) {
  return t.n < b;
}

// A default member initializer runs where the object is made, so Ticket{} changes total. Beside it, a read of total.
//@ requires total < 0x7FFFFFFF
//@ modifies total
bool default_init_beside_a_read() {
  return ticket_first(Ticket{}, total);  // BANNED
}

// The capture initializer of a lambda runs where the lambda is written. Beside it, a read of total.
//@ requires total < 0x7FFFFFFF
//@ modifies total
bool capture_beside_a_read() {
  return before(std::make_pair([k = take_next()] { return k; }, int32_t{0}).second, total);  // BANNED
}
