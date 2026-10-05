#include <algorithm>
#include <cstdint>
#include <span>
#include <utility>
#include <vector>

struct Pair {
  int32_t a = 0;
  int32_t b = 0;
  void set(int32_t v) { a = v; }
  int32_t sum() const { return a + b; }
};

//@ modifies dst
//@ ensures dst == old(src) && src == 0
void take(int32_t& dst, int32_t& src) {
  dst = src;
  src = 0;
}

int32_t add(const int32_t& a, const int32_t& b) {
  return a + b;
}

void fill(std::span<int32_t> out, std::span<const int32_t> in) {
  for (std::size_t i = 0; i < out.size() && i < in.size(); ++i) {
    out[i] = in[i];
  }
}

void sink(std::vector<int32_t> a, std::vector<int32_t> b);

// Two different objects.
void two_locals() {
  int32_t x = 1;
  int32_t y = 2;
  take(x, y);
}

// One object twice is fine when nothing in the call writes.
int32_t doubled(int32_t x) {
  return add(x, x);
}

// Two different members of one object.
void two_members(Pair& p) {
  take(p.a, p.b);
}

// The object of a const call and a member of it: no writer.
int32_t member_and_sum(const Pair& p) {
  return add(p.sum(), p.a);
}

// A member call whose argument is a copy, not a member.
void set_from_copy(Pair& p) {
  int32_t v = p.b;
  p.set(v);
}

// A member passed by value is a copy too, so the object and the member are not two names in this call.
void set_from_member(Pair& p) {
  p.set(p.b);
}

int32_t counter = 0;
const int32_t limit = 10;

// A const reference to a global in a call into std. Nothing in std can reach the State.
int32_t capped() {
  return std::min(counter, limit);
}

// A constant is not State, so a const global may bind to a const reference in any call.
int32_t over_limit(int32_t x) {
  return add(x, limit);
}

// Spans over two different vectors.
void copy_between(std::vector<int32_t>& to, const std::vector<int32_t>& from) {
  fill(to, from);
}

// A move binds an rvalue reference, and the two are different objects.
void moved(std::vector<int32_t>& a, std::vector<int32_t>& b) {
  sink(std::move(a), std::move(b));
}

// A temporary has no other name.
int32_t with_temporary(int32_t x) {
  return add(x, x + 1);
}

// Elements of one vector, each a copy.
int32_t first_two(const std::vector<int32_t>& v) {
  return v.size() < 2 ? 0 : add(v[0], v[1]);
}

// A reference that a function returns reaches what its parameter reaches.
int32_t& first_of(std::vector<int32_t>& v) {
  return v.front();
}
