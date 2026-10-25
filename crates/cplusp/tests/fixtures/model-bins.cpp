#include <cstddef>
#include <cstdint>
#include <vector>

// A class that holds a vector, as a local, a copy and a result, decision 0187.
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

  // A write to one element keeps the others.
  //@ requires i < size() && get(i) < 1000
  //@ ensures size() == old(size()) && get(i) == old(get(i)) + 1
  //@ ensures forall j :: 0 <= j < size() && j != i ==> get(j) == old(get(j))
  void add(size_t i) {
    counts_[i] = counts_[i] + 1;
  }

 private:
  std::vector<int32_t> counts_;
};

// A vector field that the init list does not name starts empty.
class Log {
 public:
  //@ ensures size() == 0 && this->first() == first
  explicit Log(int32_t first) : first_(first) {}

  //@ ensures result == first_
  int32_t first() const { return first_; }

  //@ ensures result == lines_.size()
  size_t size() const { return lines_.size(); }

 private:
  std::vector<int32_t> lines_;
  int32_t first_;
};

//@ ensures result == 2
int32_t twice() {
  Bins b(3);
  b.add(1);
  b.add(1);
  return b.get(1);
}

// A copy is a value of its own, so a write to it keeps the source.
//@ ensures result == 1
int32_t copied() {
  Bins b(2);
  b.add(0);
  Bins c = b;
  c.add(0);
  return b.get(0);
}

//@ ensures result == 0
size_t empty() {
  Log l(5);
  return l.size();
}

// The init list runs in the order of the fields: a_ takes n, then n grows, then v_ takes old(n) copies.
class Ordered {
 public:
  //@ modifies n
  //@ requires 0 < n && n < 100
  //@ ensures a() == old(n) + 1 && size() == old(n)
  explicit Ordered(size_t& n) : a_(++n), v_(n - 1, 0) {}

  //@ ensures result == a_
  size_t a() const { return a_; }

  //@ ensures result == v_.size()
  size_t size() const { return v_.size(); }

 private:
  size_t a_;
  std::vector<int32_t> v_;
};
