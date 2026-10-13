#include <cstdint>
#include <span>

// An index line above a loop that is no range-for, an index name that the function also declares, and an index line with two names,
// are refused at their lines, decision 0143.
int32_t plain(int32_t n) {
  int32_t k = 0;
  //@ index i
  while (k < n) {
    ++k;
  }
  return k;
}

int32_t clash(std::span<const int32_t> v) {
  int32_t i = 0;
  //@ index i
  for (int32_t x : v) {
    i = x;
  }
  return i;
}

int32_t two(std::span<const int32_t> v) {
  int32_t t = 0;
  //@ index i, j
  for (int32_t x : v) {
    t = x;
  }
  return t;
}

//@ index i
int32_t above(std::span<const int32_t> v) {
  return 0;
}

// An index named as a field of the object, or as a constant of the file, is a name the function already has, decision 0144.
struct Tally {
  int32_t count;
  int32_t sum(std::span<const int32_t> v) const {
    int32_t t = 0;
    //@ index count
    for (int32_t x : v) {
      t = x;
    }
    return t;
  }
};

constexpr int32_t N = 1000;

int32_t named(std::span<const int32_t> v) {
  int32_t t = 0;
  //@ index N
  for (int32_t x : v) {
    t = x;
  }
  return t;
}

// A structured binding has no rule as the loop variable, decision 0144.
struct P {
  int32_t a;
  int32_t b;
};

int32_t bound(std::span<const P> ps) {
  int32_t t = 0;
  for (auto [a, b] : ps) {
    t = 1;
  }
  return t;
}
