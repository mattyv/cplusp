#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <vector>

// The forms of a class that holds a vector that have no rule yet, decision 0187.
class Bins {
 public:
  //@ requires 0 < n && n <= 1000
  //@ ensures size() == n
  explicit Bins(size_t n) : counts_(n, 0) {}

  //@ ensures result == counts_.size()
  size_t size() const { return counts_.size(); }

  //@ requires size() < 1000
  //@ ensures size() == old(size()) + 1
  void grow() {
    counts_.push_back(0);
  }

  //@ requires i < size()
  //@ ensures size() == old(size())
  void set(size_t i) {
    counts_.at(i) = 1;
  }

  //@ requires other.size() == size()
  //@ ensures size() == old(size())
  void take(const std::vector<int32_t>& other) {
    counts_ = other;
  }

 private:
  std::vector<int32_t> counts_;
};

//@ ensures true
size_t maybe() {
  std::optional<Bins> b = Bins(2);
  return 0;
}

//@ ensures true
size_t many() {
  std::vector<Bins> v;
  return v.size();
}

//@ ensures true
size_t owned() {
  std::unique_ptr<Bins> p = std::make_unique<Bins>(2);
  return 0;
}

// A vector field with a default member initializer has no rule yet.
class Preset {
 public:
  //@ ensures size() == 3
  explicit Preset(int32_t first) : first_(first) {}

  //@ ensures result == lines_.size()
  size_t size() const { return lines_.size(); }

 private:
  std::vector<int32_t> lines_ = std::vector<int32_t>(3, 7);
  int32_t first_;
};
