#include <cstdint>

// The singleton. The classic form is the Meyers singleton: `static Tally& instance() { static Tally t; return t; }`, with a private
// constructor and the copy deleted. The gate takes it. The function-local static is no finding, because the row for statics is checked
// by the prover, and `instance()` may return a reference. A call such as `Tally::instance().bump()` passes too. The gate refuses only
// a caller that keeps the reference in a local, `Tally& t = Tally::instance();`, at that line: "Lvalue references: outside its limit.
// Limit: A parameter only. No reference member and no reference local. Two non-const reference parameters of one type carry
// `requires &a != &b`. Use a parameter, or the object itself."
// The row for statics asks each function to list the static it reads or changes, and a function-local static has no name that a
// contract can use. A caller of `instance().bump()` changes the singleton and has nothing to put in `modifies`. So the form shown
// is a class of static members, which is the singleton by construction: there is no object to make or to copy. The data is a static
// data member with a name, as in the folder global_state, and every contract lists it. The invariant is valid(), decision 0028, and
// it is a static member function that reads the data.
class Tally {
 public:
  Tally() = delete;

  //@ reads Tally::count_
  //@ ensures result == (0 <= Tally::count_ && Tally::count_ <= 1000)
  static bool valid() { return 0 <= count_ && count_ <= 1000; }

  //@ requires valid()
  //@ reads Tally::count_
  //@ ensures result == Tally::count_
  static int32_t count() { return count_; }

  //@ requires valid() && count() < 1000
  //@ modifies Tally::count_
  //@ ensures valid() && count() == old(count()) + 1
  static void bump() { count_ += 1; }

  //@ modifies Tally::count_
  //@ ensures valid() && count() == 0
  static void reset() { count_ = 0; }

 private:
  static int32_t count_;
};

int32_t Tally::count_ = 0;

// Three bumps from a count that leaves room for them. The caller lists the static, so its own callers know what it changes.
//@ requires Tally::valid() && Tally::count() <= 997
//@ modifies Tally::count_
//@ ensures Tally::valid() && Tally::count() == old(Tally::count()) + 3 && result == Tally::count()
int32_t three_bumps() {
  Tally::bump();
  Tally::bump();
  Tally::bump();
  return Tally::count();
}

//@ modifies Tally::count_
//@ ensures result == 3
int32_t reset_then_three() {
  Tally::reset();
  return three_bumps();
}
