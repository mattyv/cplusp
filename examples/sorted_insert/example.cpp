#include <cstddef>
#include <cstdint>
#include <vector>

// An insert into a sorted vector that keeps it sorted. The vector grows with push_back, and then the new element moves down by index
// writes until the one below it is not larger. The loop invariant is in the model. The contract says the vector grows by one, is
// still sorted, and holds the old elements and x, as a multiset.
//@ requires forall i, j :: 0 <= i < j < v.size() ==> v[i] <= v[j]
//@ requires v.size() < 1000000
//@ modifies v
//@ ensures v.size() == old(v.size()) + 1
//@ ensures forall i, j :: 0 <= i < j < v.size() ==> v[i] <= v[j]
//@ ensures multiset(v) == multiset(old(v)) + multiset{x}
void insert_sorted(std::vector<int32_t>& v, int32_t x) {
  v.push_back(x);
  size_t i = v.size() - 1;
  while (i > 0 && v[i - 1] > x) {
    v[i] = v[i - 1];
    i -= 1;
  }
  v[i] = x;
}
