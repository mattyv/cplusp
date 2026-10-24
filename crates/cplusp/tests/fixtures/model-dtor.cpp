#include <cstdint>

// A struct with a destructor, decision 0178. The destructor runs at the end of the block of each local of the type, in the
// reverse order of the declarations, and before each return after its value is computed. A member function, a constructor or a
// destructor can list a global, which comes after its parameters.
int32_t open_handles = 0;

//@ requires 0 <= open_handles < 1000
//@ modifies open_handles
//@ ensures open_handles == old(open_handles) + 1 && result == old(open_handles)
int32_t acquire() {
  return open_handles++;
}

//@ requires open_handles > 0
//@ modifies open_handles
//@ ensures open_handles == old(open_handles) - 1
void release(int32_t) {
  open_handles -= 1;
}

class Guard {
 public:
  //@ requires 0 <= open_handles < 1000
  //@ modifies open_handles
  //@ ensures open_handles == old(open_handles) + 1 && handle() == old(open_handles)
  Guard() : handle_(acquire()) {}

  //@ requires open_handles > 0
  //@ modifies open_handles
  //@ ensures open_handles == old(open_handles) - 1
  ~Guard() { release(handle_); }

  //@ ensures result == handle_
  int32_t handle() const { return handle_; }

 private:
  int32_t handle_;
};

//@ requires 0 <= open_handles < 1000
//@ modifies open_handles
//@ ensures open_handles == old(open_handles) && result == old(open_handles)
int32_t use_one() {
  Guard g;
  return g.handle();
}

// Two guards die in the reverse order, and a guard in a nested block dies at its end.
//@ requires 0 <= open_handles < 998
//@ modifies open_handles
//@ ensures open_handles == old(open_handles) && result == old(open_handles) + 2
int32_t two_then_one() {
  Guard a;
  int32_t inside = 0;
  {
    Guard b;
    inside = open_handles;
  }
  return inside;
}

// A return inside an if destroys the guard too.
//@ requires 0 <= open_handles < 1000
//@ modifies open_handles
//@ ensures open_handles == old(open_handles) && result == (take ? old(open_handles) : -1)
int32_t maybe_handle(bool take) {
  Guard g;
  if (take) {
    return g.handle();
  }
  return -1;
}

// A member function that lists a global.
struct Tally {
  int32_t n_;

  //@ requires open_handles < 1000 && n_ < 1000
  //@ modifies open_handles
  //@ ensures open_handles == old(open_handles) + 1 && n_ == old(n_) + 1
  void bump_both() {
    open_handles += 1;
    n_ += 1;
  }
};

//@ requires 0 <= open_handles < 1000 && t.n_ < 1000
//@ modifies open_handles, t
//@ ensures open_handles == old(open_handles) + 1 && t.n_ == old(t.n_) + 1
void bump_through(Tally& t) {
  t.bump_both();
}

// A guard in a branch, in a loop body and in a case dies at the end of each. A `return;` and the end of a void function destroy
// the live guards.
//@ requires 0 <= open_handles < 1000
//@ modifies open_handles
//@ ensures open_handles == old(open_handles)
void in_branch(bool take) {
  if (take) {
    Guard g;
  }
}

//@ requires 0 <= open_handles < 1000
//@ modifies open_handles
//@ ensures open_handles == old(open_handles)
void in_loop(int32_t n) {
  int32_t start = open_handles;
  int32_t i = 0;
  //@ invariant open_handles == start
  //@ decreases n - i
  while (i < n) {
    Guard g;
    i += 1;
  }
}

enum class Mode { kOne, kTwo };

//@ requires 0 <= open_handles < 1000
//@ modifies open_handles
//@ ensures open_handles == old(open_handles)
void in_case(Mode m) {
  switch (m) {
    case Mode::kOne: {
      Guard g;
      break;
    }
    case Mode::kTwo:
      break;
  }
}

//@ requires 0 <= open_handles < 1000
//@ modifies open_handles
//@ ensures open_handles == old(open_handles)
void early(bool stop) {
  Guard g;
  if (stop) {
    return;
  }
}

// The value of a return is computed before the guard dies, also when it reads the global, or when it runs a call only sometimes.
//@ requires 0 <= open_handles < 1000
//@ modifies open_handles
//@ ensures open_handles == old(open_handles) && result == old(open_handles) + 1
int32_t count_inside() {
  Guard g;
  return open_handles;
}

//@ requires 0 <= open_handles < 1000
//@ modifies open_handles
//@ ensures open_handles == old(open_handles) && result == (take ? old(open_handles) : -1)
int32_t pick(bool take) {
  Guard g;
  return take ? g.handle() : -1;
}

// A return inside a bare block destroys the inner guard, then the outer one.
//@ requires 0 <= open_handles < 999
//@ modifies open_handles
//@ ensures open_handles == old(open_handles) && result == old(open_handles) + 1
int32_t nested_return() {
  Guard a;
  {
    Guard b;
    return b.handle();
  }
}
