#include <cstdint>
#include <memory>

// The forms of a state that gives the next state that have no rule, decision 0199.
struct Count {
  int32_t v;

  // A body that writes a local is no pure body, also with an early return.
  //@ ensures true
  int32_t step() const {
    int32_t k = v;
    k = v;
    if (k < 0) {
      return 0;
    }
    return k;
  }

  //@ ensures result == (step() >= 0)
  bool ok() const { return step() >= 0; }
};

struct Cell {
  int32_t value = 1;
};

class Holder {
 public:
  //@ ensures true
  Holder() : c_(std::make_unique<Cell>()) {}

  // A field write from a move of a local.
  //@ ensures true
  void take() {
    std::unique_ptr<Cell> n = std::make_unique<Cell>();
    c_ = std::move(n);
  }

 private:
  std::unique_ptr<Cell> c_;
};
