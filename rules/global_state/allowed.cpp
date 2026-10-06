#include <cstdint>

int32_t total = 0;
const int32_t limit = 100;

struct Tally {
  static int32_t n;
};

int32_t Tally::n = 0;

// A write is on the modifies line.
//@ requires total < limit
//@ modifies total
//@ ensures total == old(total) + 1
void bump() {
  total += 1;
}

// A read is on the reads line. The constant needs no line.
//@ reads total
//@ ensures result == (total < limit)
bool below() {
  return total < limit;
}

// A static data member by its qualified name.
//@ requires Tally::n < 0x7FFFFFFF
//@ modifies Tally::n
//@ ensures Tally::n == old(Tally::n) + 1
void count() {
  Tally::n += 1;
}

// A caller lists what its callee changes.
//@ requires total < limit - 1
//@ modifies total
//@ ensures total == old(total) + 2
void twice() {
  bump();
  bump();
}

// Members are implicit, decision 0028. No line names them.
struct Counter {
  int32_t n = 0;
  //@ requires n < 0x7FFFFFFF
  //@ ensures n == old(n) + 1
  void step() {
    ++n;
  }
};

// An unqualified name on the line is fine when one variable has it.
//@ requires Tally::n < 0x7FFFFFFF
//@ modifies n
void count_short() {
  Tally::n += 1;
}

template <typename T>
struct Box {
  static int32_t items;
};

template <typename T>
int32_t Box<T>::items = 0;

// The static member of a class template, named without the template arguments, as the bot writes it.
//@ requires Box::items < 0x7FFFFFFF
//@ modifies Box::items
void bump_box() {
  Box<int32_t>::items += 1;
}

#include <algorithm>
#include <vector>

// A lambda runs inside the function that passes it, so the function's lines cover what it does.
//@ modifies total
void sum_listed(const std::vector<int32_t>& v) {
  std::ranges::for_each(v, [](int32_t x) { total += x; });
}

// A template's lines go above the template, as in examples/templates, and its instantiation is judged against them.
//@ requires total < 0x7FFFFFFF
//@ modifies total
template <typename T>
void bump_with(T) {
  total += 1;
}

//@ requires total < 0x7FFFFFFF
//@ modifies total
void use_bump_with() {
  bump_with(int32_t{1});
}

#include <cstddef>

struct Guard {
  //@ requires total < 0x7FFFFFFF
  //@ modifies total
  ~Guard() {
    total += 1;
  }
};

// A const member call on a std container runs none of the element's own functions. Only the code the compiler generates for the
// call counts, decision 0037.
//@ ensures result == v.size()
std::size_t how_many(const std::vector<Guard>& v) {
  return v.size();
}

struct Base {
  virtual ~Base() = default;
  //@ requires total < 0x7FFFFFFF
  //@ modifies total
  virtual void act() {
    total += 1;
  }
};

// An override lists no more than the function it overrides. This one changes nothing.
struct Quiet : Base {
  void act() override {}
};

// A call through the base brings the base's lines, and they hold for every override.
//@ requires total < 0x7FFFFFFF
//@ modifies total
void act_on(Base& b) {
  b.act();
}
