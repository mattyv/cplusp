#include <cstddef>
#include <cstdint>
#include <vector>

// Claims about a class that holds a vector that do not hold, decision 0187.
class Bins {
 public:
  //@ requires 0 < n && n <= 1000
  //@ ensures size() == n && forall i :: 0 <= i < n ==> get(i) == 0
  explicit Bins(size_t n) : counts_(n, 0) {}

  //@ ensures result == counts_.size()
  size_t size() const { return counts_.size(); }

  //@ requires i < size()
  //@ ensures result == counts_[i]
  int32_t get(size_t i) const { return counts_.at(i); }

  //@ requires i < size() && get(i) < 1000
  //@ ensures size() == old(size()) && get(i) == old(get(i)) + 1
  //@ ensures forall j :: 0 <= j < size() && j != i ==> get(j) == old(get(j))
  void add(size_t i) {
    counts_[i] = counts_[i] + 1;
  }

  // The index can be the size, one past the end.
  //@ requires i <= size()
  //@ ensures size() == old(size())
  void poke(size_t i) {
    counts_[i] = 1;
  }

 private:
  std::vector<int32_t> counts_;
};

// Each count starts at zero.
//@ ensures result == 1
int32_t start() {
  Bins b(2);
  return b.get(0);
}

// A copy is a value of its own, so the source keeps its count.
//@ ensures result == 2
int32_t copied() {
  Bins b(2);
  b.add(0);
  Bins c = b;
  c.add(0);
  return b.get(0);
}

// The vector field comes after a_, so it sees n after the step.
class Ordered {
 public:
  //@ modifies n
  //@ requires 0 < n && n < 100
  //@ ensures a() == old(n) + 1 && size() == old(n) - 1
  explicit Ordered(size_t& n) : a_(++n), v_(n - 1, 0) {}

  //@ ensures result == a_
  size_t a() const { return a_; }

  //@ ensures result == v_.size()
  size_t size() const { return v_.size(); }

 private:
  size_t a_;
  std::vector<int32_t> v_;
};
