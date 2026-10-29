#include <cstdint>
#include <utility>
#include <vector>

// A std::move of a value that is not trivially copyable keeps its sentence, decision 0212.
struct Bag {
  std::vector<int32_t> xs;
};

class Holder {
 public:
  //@ ensures true
  explicit Holder(Bag b) : b_(std::move(b)) {}

 private:
  Bag b_;
};
