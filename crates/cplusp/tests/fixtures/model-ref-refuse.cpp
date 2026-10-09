#include <cstdint>

// A name on the modifies line that is no reference parameter, a reference that the modifies line does not name, a write back to a
// parameter by value, and a write back to a field, are refused at their lines, decision 0108.
struct Pair {
  int32_t a = 0;
  int32_t b = 0;
};

//@ modifies n
int32_t by_value(int32_t n) {
  return n;
}

void unlisted(int32_t& x) {
  x = 1;
}

//@ modifies x
void set(int32_t& x) {
  x = 2;
}

void pass_value(int32_t y) {
  set(y);
}

int32_t to_field() {
  Pair p{1, 2};
  set(p.a);
  return p.a;
}

// A modifies line of another form, and a name with parts, decision 0110.
//@ modifies x,
void comma(int32_t& x) {
  x = 3;
}

//@ modifies Tally::count_
int32_t qualified() {
  return 0;
}

// A function whose body is refused keeps its header with its outs, so its caller resolves, decision 0108.
//@ modifies x
void shifted(int32_t& x) {
  x <<= 1;
}

int32_t use_shifted() {
  int32_t a = 1;
  shifted(a);
  return a;
}
