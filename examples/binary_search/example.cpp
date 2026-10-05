#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>

// A binary search over a sorted span. It returns the index of an element equal to the key, or nothing. The contract says what each answer
// means: an index is in range and holds the key, and no answer means that no element equals the key. The span must be sorted.
// The midpoint is lo + (hi - lo) / 2 and never (lo + hi) / 2. The sum lo + hi can pass the largest size_t when the span is long, and
// it then wraps to a small number and the search goes wrong. This is the old bug that sat in the Java library for years. The prover
// asks for the same bound, and the span size alone cannot give it. The difference hi - lo never goes below zero, because lo <= hi, and
// the midpoint stays in [lo, hi). The loop invariants are in the contract notation, and they are the same in example.dfy. The elements
// below lo are all smaller than the key, and the elements from hi up are all larger.
//@ requires forall i, j :: 0 <= i < j < a.size() ==> a[i] <= a[j]
//@ ensures result.has_value() ==> *result < a.size() && a[*result] == key
//@ ensures !result.has_value() ==> forall i :: 0 <= i < a.size() ==> a[i] != key
std::optional<size_t> binary_search(std::span<const int32_t> a, int32_t key) {
  size_t lo = 0;
  size_t hi = a.size();
  //@ invariant 0 <= lo <= hi <= a.size()
  //@ invariant forall i :: 0 <= i < lo ==> a[i] < key
  //@ invariant forall i :: hi <= i < a.size() ==> a[i] > key
  while (lo < hi) {
    size_t mid = lo + (hi - lo) / 2;
    if (a[mid] < key) {
      lo = mid + 1;
    } else if (a[mid] > key) {
      hi = mid;
    } else {
      return mid;
    }
  }
  return std::nullopt;
}

// A caller proves its answer from the contract alone.
//@ requires forall i, j :: 0 <= i < j < a.size() ==> a[i] <= a[j]
//@ ensures result == exists i :: 0 <= i < a.size() && a[i] == key
bool contains(std::span<const int32_t> a, int32_t key) {
  return binary_search(a, key).has_value();
}
