#include <algorithm>
#include <array>
#include <cstdint>
#include <functional>
#include <span>
#include <vector>
const int32_t& first() {
  int32_t local = 1;
  return local;  // BANNED
}

int32_t* address() {
  int32_t local = 1;
  return &local;  // BANNED
}

// A reference to a local escapes through a call that returns a reference, decision 0182.
const int32_t& id(const int32_t& x) {
  return x;
}

const int32_t& second(const int32_t& a, const int32_t& b) {
  return b;
}

const int32_t& through() {
  int32_t local = 1;
  return id(local);  // BANNED
}

const int32_t& by_value(int32_t v) {
  return id(v);  // BANNED
}

const int32_t& in_second(const int32_t& x) {
  int32_t local = 1;
  return second(x, local);  // BANNED
}

struct Box {
  int32_t v;

  const int32_t& get() const {
    return v;
  }
};

const int32_t& member_of_local() {
  Box b{1};
  return b.get();  // BANNED
}

const int32_t* pass(const int32_t* p) {
  return p;
}

const int32_t* address_through() {
  int32_t local = 1;
  return pass(&local);  // BANNED
}

const int32_t* address_of_call() {
  int32_t local = 1;
  return &id(local);  // BANNED
}

const int32_t& chain() {
  int32_t local = 1;
  return id(id(local));  // BANNED
}

const int32_t& either(const int32_t& x, bool c) {
  int32_t local = 1;
  return c ? id(x) : id(local);  // BANNED
}

const int32_t& larger(const int32_t& x) {
  int32_t local = 1;
  return std::max(local, x);  // BANNED
}

const int32_t& in_loop(const int32_t& x) {
  std::vector<int32_t> v{1, 2};
  for (const int32_t& e : v) {
    return e;  // BANNED
  }
  return x;
}

const int32_t& loop_copy(const std::vector<int32_t>& v, const int32_t& x) {
  for (int32_t e : v) {
    return id(e);  // BANNED
  }
  return x;
}

std::span<const int32_t> view() {
  std::array<int32_t, 2> a{1, 2};
  return a;  // BANNED
}

const int32_t& captured() {
  int32_t x = 1;
  return std::invoke([x]() -> const int32_t& { return id(x); });  // BANNED
}

struct Two {
  int32_t x;
  int32_t y;
};

const int32_t& in_binding() {
  Two t{1, 2};
  auto [x, y] = t;
  return id(x);  // BANNED
}
