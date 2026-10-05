#include <cstddef>
#include <cstdint>
#include <span>

// A dot product of two spans with a 64-bit accumulator. The product of two int32_t is an int product, and it can overflow at these
// bounds, so one factor is widened first. The bounds on the elements and on the length keep the sum inside int64_t. The invariant
// carries the same bound for the sum so far. Dot is the specification function, and example.dfy defines it as the sum of the products.
int64_t dot(std::span<const int32_t> a, std::span<const int32_t> b) {
  int64_t acc = 0;
  //@ invariant 0 <= i <= a.size()
  //@ invariant acc == Dot(a[..i], b[..i])
  //@ invariant -1000000000000 * i <= acc <= 1000000000000 * i
  for (size_t i = 0; i < a.size(); ++i) {
    acc += static_cast<int64_t>(a[i]) * b[i];
  }
  return acc;
}
