#include <cstdint>
#include <optional>
#include <vector>

// A copy of a struct with a destructor, as a result, a parameter, a field, a temporary and a container, a destructor with no
// contract, and a local in the head of a for, decision 0178.
int32_t open_handles = 0;

class Guard {
 public:
  //@ ensures true
  Guard() : handle_(0) {}

  //@ requires open_handles > 0
  //@ modifies open_handles
  //@ ensures open_handles == old(open_handles) - 1
  ~Guard() { open_handles -= 1; }

 private:
  int32_t handle_;
};

//@ requires open_handles > 0
//@ modifies open_handles
//@ ensures true
Guard make() {
  Guard g;
  return g;
}

//@ ensures result == 0
int32_t take(Guard g) {
  return 0;
}

struct Holder {
  Guard guard_;
  int32_t n_;
};

class Quiet {
 public:
  //@ ensures true
  Quiet() : n_(0) {}
  ~Quiet() {}
 private:
  int32_t n_;
};

//@ ensures result == 1
int32_t use_quiet() {
  Quiet q;
  return 1;
}

// A temporary, a const reference, a sequence, an optional and a guard in the head of a for, decision 0178.
struct Lock {
  int32_t id;
  //@ requires open_handles > 0
  //@ modifies open_handles
  //@ ensures open_handles == old(open_handles) - 1
  ~Lock() { open_handles -= 1; }
};

//@ requires open_handles > 0
//@ modifies open_handles
//@ ensures result == 5
int32_t brace_temp() {
  return Lock{5}.id;
}

//@ requires open_handles > 0
//@ modifies open_handles
//@ ensures true
void discard() {
  make();
}

//@ ensures result == 0
int32_t peek(const Guard& g) {
  return 0;
}

//@ modifies open_handles
//@ ensures result == v.size()
uint64_t copy_all(const std::vector<Lock>& v) {
  return v.size();
}

//@ requires open_handles > 0
//@ modifies open_handles
//@ ensures result == 0
int32_t maybe_lock() {
  std::optional<Lock> o = std::nullopt;
  return 0;
}

//@ requires open_handles > 0
//@ modifies open_handles
//@ ensures true
void in_head() {
  int32_t i = 0;
  for (Guard g; i < 1; ++i) {
  }
}
