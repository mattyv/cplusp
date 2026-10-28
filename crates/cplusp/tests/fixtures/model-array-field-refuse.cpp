#include <array>
#include <cstdint>

// The forms of a std::array field that have no rule, decision 0196.
class NoStart {
 public:
  //@ ensures true
  explicit NoStart(int32_t k) : k_(k) {}

 private:
  std::array<int32_t, 4> items_;
  int32_t k_;
};

// A default member initializer with values keeps the sentence of today.
class Listed {
 public:
  //@ ensures true
  Listed() : k_(0) {}

 private:
  std::array<int32_t, 3> items_{1, 2, 3};
  int32_t k_;
};

// The gate does not read a class template, so the translator alone gives the sentence.
template <typename T>
class Box {
 public:
  //@ ensures true
  explicit Box(T k) : k_(k) {}

 private:
  std::array<T, 4> a_;
  T k_;
};

template class Box<int32_t>;
