#include <cstdint>

// Member functions with no rule yet are refused at their lines, decision 0089.
struct Counter {
  int32_t n_;

  int32_t grow() & {
    n_ = n_ + 1;
    return n_;
  }

  static int32_t zero() {
    return 0;
  }

  //@ ensures result == m_
  int32_t wrong() const {
    return n_;
  }
};
