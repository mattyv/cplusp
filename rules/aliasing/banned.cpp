#include <cstdint>
#include <memory>
#include <span>
#include <vector>

struct Pair {
  int32_t a = 0;
  int32_t b = 0;
  void take(int32_t& v) {
    a = v;
    v = 0;
  }
  int32_t sum() const { return a + b; }
};

void take(int32_t& dst, int32_t& src) {
  dst = src;
  src = 0;
}

int32_t set_and_read(int32_t& a, const int32_t& b) {
  a = 1;
  return b;
}

void swap_fields(Pair& p, int32_t& field) {
  p.a = field;
  field = 0;
}

void append(std::vector<int32_t>& w, const std::vector<int32_t>& v) {
  for (const int32_t x : v) {
    w.push_back(x);
  }
}

void fill(std::span<int32_t> out, std::span<const int32_t> in) {
  for (std::size_t i = 0; i < out.size() && i < in.size(); ++i) {
    out[i] = in[i];
  }
}

void bump(int32_t& x) {
  x += 1;
}

int32_t counter = 0;

// Two non-const references to one object.
void same_object() {
  int32_t x = 1;
  take(x, x);  // BANNED
}

// A non-const and a const reference to one object. The result is 1, the model says 0.
int32_t const_alias() {
  int32_t x = 0;
  return set_and_read(x, x);  // BANNED
}

// A struct and one of its members: different types, one storage.
void struct_and_member(Pair& p) {
  swap_fields(p, p.a);  // BANNED
}

// A const container and a non-const one. The loop reads what push_back frees.
void same_vector(std::vector<int32_t>& v) {
  append(v, v);  // BANNED
}

// Two spans cut from one buffer.
void same_buffer(std::vector<int32_t>& v) {
  fill(v, v);  // BANNED
}

// The object of a non-const member call and one of its members, by reference.
void object_and_member(Pair& p) {
  p.take(p.b);  // BANNED
}

// Through a handle: the owner and what it owns.
void owner_and_owned(std::unique_ptr<int32_t>& p, int32_t& x);

void handle(std::unique_ptr<int32_t>& p) {
  owner_and_owned(p, *p);  // BANNED
}

// The loop variable of a range-for is a name for an element of the range, so it and an element of the range are two names.
void element_and_range(std::vector<int32_t>& v) {
  for (int32_t& e : v) {
    take(e, v[0]);  // BANNED
  }
}

// A global is the State as well, so a reference to it is a second name.
void global_by_reference() {
  bump(counter);  // BANNED
}

std::span<int32_t> head(std::vector<int32_t>& v) {
  return std::span<int32_t>(v).first(1);
}

// A span cut by a user function is still a name for the buffer it was cut from.
void cut_twice(std::vector<int32_t>& v) {
  fill(head(v), head(v));  // BANNED also: evaluation_order
}

void cut_and_whole(std::vector<int32_t>& v) {
  fill(head(v), v);  // BANNED also: evaluation_order
}

void bump_two(int32_t& x, int32_t& y = counter);

// A default argument is an argument. Here it binds a global to a reference.
void defaulted() {
  int32_t x = 0;
  bump_two(x);  // BANNED
}

struct Holder {
  int32_t v = 0;
};

Holder holder;

// A function that returns a reference may return only what its parameters reach. A global that escapes this way is a
// global passed by reference at every call of the function.
int32_t& name_of_counter() {
  return counter;  // BANNED
}

int32_t& name_of_field() {
  return holder.v;  // BANNED
}
