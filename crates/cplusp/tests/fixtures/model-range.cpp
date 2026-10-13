#include <cstdint>
#include <span>
#include <vector>

// A range-for is a loop over the indexes of its sequence. The index line names the index, so an invariant and an assert can read it,
// decision 0143. Sum is a function of the companion file.
//@ requires v.size() <= 1000
//@ requires forall j :: 0 <= j < v.size() ==> -1000 <= v[j] <= 1000
//@ ensures result == Sum(v)
int32_t total(const std::vector<int32_t>& v) {
  int32_t t = 0;
  //@ index i
  //@ invariant t == Sum(v[..i])
  //@ invariant -1000 * i <= t && t <= 1000 * i
  for (const int32_t x : v) {
    //@ assert v[..i + 1][..i] == v[..i]
    t += x;
  }
  //@ assert v[..v.size()] == v
  return t;
}

// A loop that needs no invariant needs no index line.
//@ ensures result ==> exists j :: 0 <= j < v.size() && v[j] == 0
bool any_zero(std::span<const int32_t> v) {
  for (int32_t x : v) {
    if (x == 0) {
      return true;
    }
  }
  return false;
}

// Two range-fors on one line, each with no index line, get their own index, decision 0144.
int32_t pairs(std::span<const int32_t> v, std::span<const int32_t> w) {
  int32_t t = 0;
  for (int32_t x : v) for (int32_t y : w) { t = x; t = y; }
  return t;
}
