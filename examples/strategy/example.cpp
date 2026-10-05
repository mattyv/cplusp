#include <cstdint>

// A strategy is an interface with one operation and a contract, and the code that uses it takes the strategy as a parameter.
// The classic form also has a Context class that keeps the strategy in a member. The gate refuses a reference member at its line:
// "Lvalue references: outside its limit. Limit: A parameter only. No reference member and no reference local. Two non-const
// reference parameters of one type carry `requires &a != &b`. Use a parameter, or the object itself." It refuses a pointer member
// in the same way: "Non-owning raw pointer to one object: outside its limit. Limit: A parameter only. One object, no ownership, no
// arithmetic. No pointer member and no pointer local. Use a reference, or a value." So the strategy stays a parameter, and the
// function that runs it is the context.
struct Strategy {
  virtual ~Strategy() = default;
  // The invariant of each strategy, decision 0028. The interface cannot know the fields, so it is virtual.
  virtual bool valid() const = 0;
  //@ requires valid() && 0 <= x <= 1000
  //@ ensures 0 <= result <= 1000000
  virtual int32_t apply(int32_t x) const = 0;
};

// A strategy with no data.
class Squared final : public Strategy {
 public:
  //@ ensures result == true
  bool valid() const override { return true; }

  //@ requires valid() && 0 <= x <= 1000
  //@ ensures result == x * x
  int32_t apply(int32_t x) const override { return x * x; }
};

class Scaled final : public Strategy {
 public:
  //@ requires 0 <= k <= 1000
  //@ ensures valid() && this->k_ == k
  explicit Scaled(int32_t k) : k_(k) {}

  //@ ensures result == (0 <= k_ && k_ <= 1000)
  bool valid() const override { return 0 <= k_ && k_ <= 1000; }

  //@ requires valid() && 0 <= x <= 1000
  //@ ensures result == x * k_
  int32_t apply(int32_t x) const override { return x * k_; }

 private:
  int32_t k_;
};

// The context. It proves from the contract of Strategy alone, so it holds for every strategy. Both calls read the same strategy,
// and a const function gives the same answer for the same argument.
//@ requires s.valid() && 0 <= x < 1000
//@ ensures 0 <= result <= 2000000 && result == s.apply(x) + s.apply(x + 1)
int32_t apply_to_neighbours(const Strategy& s, int32_t x) {
  return s.apply(x) + s.apply(x + 1);
}

// 4 squared is 16 and 5 squared is 25. Three times 4 is 12 and three times 5 is 15.
//@ ensures result == 68
int32_t demo() {
  const Squared sq;
  const Scaled sc(3);
  const int32_t a = apply_to_neighbours(sq, 4);
  const int32_t b = apply_to_neighbours(sc, 4);
  return a + b;
}
