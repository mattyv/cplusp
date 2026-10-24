#include <cstdint>
#include <span>
#include <vector>
int32_t first() {
  int32_t local = 1;
  return local;
}

// A reference that a parameter or `this` reaches may come back through a call, decision 0182.
const int32_t& id(const int32_t& x) {
  return x;
}

const int32_t& through(const int32_t& x) {
  return id(x);
}

struct Box {
  int32_t v;

  const int32_t& get() const {
    return v;
  }

  const int32_t& again() const {
    return get();
  }
};

const int32_t& member_of_param(const Box& b) {
  return b.get();
}

// A pointer or a span by value is a handle. What it points to lives after the call.
const int32_t* pass(const int32_t* p) {
  return p;
}

const int32_t& deref(const int32_t* p) {
  return *p;
}

const int32_t& member_through_pointer(const Box* b) {
  return b->get();
}

const int32_t& first_of(std::span<const int32_t> s) {
  return s[0];
}

const int32_t& first_in(const std::vector<int32_t>& v, const int32_t& x) {
  for (const int32_t& e : v) {
    return id(e);
  }
  return x;
}
