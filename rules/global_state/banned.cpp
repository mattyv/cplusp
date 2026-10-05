#include <cstdint>

int32_t total = 0;

struct Tally {
  static int32_t n;
};

int32_t Tally::n = 0;

//@ requires total < 0x7FFFFFFF
//@ modifies total
//@ ensures total == old(total) + 1
void bump() {
  total += 1;
}

// A write with no modifies line.
//@ requires total < 0x7FFFFFFF
//@ ensures total == old(total) + 1
void bump_unlisted() {
  total += 1;  // BANNED
}

// A read with no reads line.
bool positive() {
  return total > 0;  // BANNED
}

// A reads line where the body writes.
//@ reads total
void reset() {
  total = 0;  // BANNED
}

// The wrong name on the line.
//@ requires total < 0x7FFFFFFF
//@ modifies Tally::n
void bump_wrong() {
  total += 1;  // BANNED
}

// A call to a function whose line lists a global, with no line of its own.
//@ requires total < 0x7FFFFFFF
void through_a_call() {
  bump();  // BANNED
}

#include <algorithm>
#include <cerrno>
#include <vector>

// A lambda body runs inside the function that passes it, so its write is the function's write.
void sum_all(const std::vector<int32_t>& v) {
  std::ranges::for_each(v, [](int32_t x) { total += x; });  // BANNED
}

struct Guard {
  //@ requires total < 0x7FFFFFFF
  //@ modifies total
  ~Guard() {
    total += 1;
  }
};

// A destructor runs at the end of the scope. Its line counts at the local that owns it.
void scoped() {
  Guard g;  // BANNED
}

struct Noisy {
  //@ requires total < 0x7FFFFFFF
  //@ modifies total
  Noisy() {
    total += 1;
  }
};

struct Wrap {
  Noisy n;
};

// An implicit constructor runs the constructors of its members, and their lines count.
void wrapped() {
  Wrap w;  // BANNED
}

// A default member initialiser runs where the object is made.
struct Counted {
  int32_t v = (total += 1);  // BANNED
};

Counted make_counted() {
  return Counted{};
}

namespace std {
inline int32_t evil = 0;
}

// A global is state wherever it is declared. Only a system header's globals are not ours.
void poison() {
  std::evil += 1;  // BANNED
}

//@ requires total < 0x7FFFFFFF
//@ modifies total
void bump_by(int32_t x) {
  total += x;
}

// A template body is read at its instantiation, where the callee is known.
template <typename T>
void once(T x) {
  bump_by(x);  // BANNED
}

void use_once() {
  once<int32_t>(1);
}

int32_t& hidden();

// A reference from a function this file does not define may reach any global.
void through_hidden() {
  hidden() = 5;  // BANNED
}

void clear_errno() {
  errno = 0;  // BANNED
}

template <typename T>
struct Box {
  static int32_t n;
};

template <typename T>
int32_t Box<T>::n = 0;

//@ requires Box::n < 0x7FFFFFFF
//@ modifies Box::n
void bump_box() {
  Box<int32_t>::n += 1;
}

// The callee's line names the static member of a class template, and the caller has no line.
void twice_box() {
  bump_box();  // BANNED
}

struct A {
  static int32_t n;
};

struct B {
  static int32_t n;
};

int32_t A::n = 0;
int32_t B::n = 0;

// An unqualified name on the line names one variable. Two statics called n make it name none.
//@ modifies n
void both() {
  A::n += 1;  // BANNED
  B::n += 1;  // BANNED
}
