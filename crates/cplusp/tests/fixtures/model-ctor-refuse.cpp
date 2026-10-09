#include <cstdint>

// Constructors with no rule yet are refused at their lines, decision 0094.
struct Pair {
  int32_t a_;
  int32_t b_;

  explicit Pair(int32_t a) : a_(a), b_(0) {
    a_ = 1;
  }

  Pair(int32_t a, int32_t b) : a_(a) {}

  Pair() : Pair(0) {}
};
