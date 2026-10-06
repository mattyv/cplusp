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

// A destructor runs at the end of the scope, and the compiler puts the call at the brace that ends it, decision 0037.
void scoped() {
  Guard g;
}  // BANNED

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

#include <memory>
#include <utility>

struct Deep0 {
  //@ requires total < 0x7FFFFFFF
  //@ modifies total
  ~Deep0() {
    total += 1;
  }
};

struct Deep1 { Deep0 d; };
struct Deep2 { Deep1 d; };
struct Deep3 { Deep2 d; };
struct Deep4 { Deep3 d; };
struct Deep5 { Deep4 d; };
struct Deep6 { Deep5 d; };
struct Deep7 { Deep6 d; };
struct Deep8 { Deep7 d; };
struct Deep9 { Deep8 d; };

// 3. The destructor nine members down runs as surely as one at the top. No depth ends in a pass, decision 0036.
void deep_scope() {
  Deep9 d{};
}  // BANNED

struct Mover {
  int32_t v = 0;
  Mover() = default;
  //@ requires total < 0x7FFFFFFF
  //@ modifies total
  Mover(Mover&& other) : v(other.v) {
    total += 1;
  }
  Mover& operator=(Mover&& other) = default;
};

// A std template over a user class runs the class's own constructors and destructor, and their lines count. std::swap
// moves through the constructor.
void swapped(Mover& a, Mover& b) {
  std::swap(a, b);  // BANNED
}

void grown(std::vector<Guard>& v) {
  v.emplace_back();  // BANNED
}

void owned() {
  std::unique_ptr<Guard> g = std::make_unique<Guard>();
}  // BANNED

// A function passed by name runs inside the std call, so its lines count at the call.
void each_by_name(const std::vector<int32_t>& v) {
  std::ranges::for_each(v, bump_by);  // BANNED
}

// A parameter named after a global does not hide the global from the caller.
//@ requires total < 0x7FFFFFFF
//@ modifies total
void sneaky(int32_t total) {
  ::total += total;
}

void calls_sneaky() {
  sneaky(1);  // BANNED
}

// An unqualified name names one variable in the whole translation unit, declared above the function or below it.
struct Outer {
  //@ modifies m
  void f() {
    m += 1;  // BANNED
    Inner::m += 1;  // BANNED
  }
  struct Inner {
    static int32_t m;
  };
  static int32_t m;
};

int32_t Outer::m = 0;
int32_t Outer::Inner::m = 0;

namespace ns1 {
struct C {
  static int32_t k;
};
int32_t C::k = 0;
}  // namespace ns1

namespace ns2 {
struct C {
  static int32_t k;
};
int32_t C::k = 0;
}  // namespace ns2

// A qualified name names one variable too. Two variables end in C::k, so the line names neither.
//@ modifies C::k
void two_cs() {
  ns1::C::k += 1;  // BANNED
  ns2::C::k += 1;  // BANNED
}

//@ ensures result == v
int32_t take_const(const int32_t& v) {
  return v;
}

// A reference from a function this file does not define may reach any global, read through a const parameter too.
int32_t read_hidden() {
  return take_const(hidden());  // BANNED
}

struct Holder2 {
  int32_t v = 0;
  int32_t get() const { return v; }
};

Holder2& hidden_holder();

int32_t read_hidden_holder() {
  return hidden_holder().get();  // BANNED
}

// delete runs the destructor of what it deletes.
void drop(Guard* g) {
  delete g;  // BANNED also: raw_allocation
}

void opaque_step();

// 2. A callee with no body here and no contract lines may change any global, decision 0036.
void calls_opaque() {
  opaque_step();  // BANNED
}

void opaque_each(int32_t x);

// 4. A function with no body here and no lines, passed by name into a std algorithm. The algorithm calls it, so the gate refuses the
// call where the algorithm is called, decision 0037.
void each_opaque(const std::vector<int32_t>& v) {
  std::ranges::for_each(v, opaque_each);  // BANNED
}

namespace std {
void evil_step();
}

// 5. A function this file declares in namespace std is no part of the standard library. The location decides, not the namespace.
void calls_evil() {
  std::evil_step();  // BANNED
}

struct Copied {
  int32_t v = 0;
  Copied() = default;
  //@ requires total < 0x7FFFFFFF
  //@ modifies total
  Copied(const Copied& other) : v(other.v) {
    total += 1;
  }
  Copied& operator=(const Copied&) = default;
};

// 6. A copy assignment of a std container copies its elements, and the element's copy constructor has a line.
void copy_all(std::vector<Copied>& a, const std::vector<Copied>& b) {
  a = b;  // BANNED
}

struct Base {
  virtual ~Base() = default;
  virtual void act() {}
};

struct Loud : Base {
  //@ requires total < 0x7FFFFFFF
  //@ modifies total
  void act() override {  // BANNED
    total += 1;
  }
};

// 7. An override lists no more than the function it overrides, decision 0037. A call through the base brings the base's lines, which
// list nothing, so this caller needs no line.
void act_on(Base& b) {
  b.act();
}

struct Alarm {
  //@ requires total < 0x7FFFFFFF
  //@ modifies total
  virtual ~Alarm() {
    total += 1;
  }
};

struct Siren : Alarm {};

// 8. A unique_ptr to a base deletes through the virtual destructor, inside the std code. The base's lines count at the brace that
// ends the scope, decision 0037. The temporary that make_unique returns has a destructor of its own, on its line.
void owned_base() {
  std::unique_ptr<Alarm> a = std::make_unique<Siren>();  // BANNED
}  // BANNED
