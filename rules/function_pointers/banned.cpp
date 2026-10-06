#include <cstdint>
#include <functional>
#include <vector>

struct Widget {
  int32_t size(int32_t scale);
};

using Handler = int32_t (*)(int32_t);  // BANNED

int32_t apply(int32_t (*f)(int32_t), int32_t x) {  // BANNED
  return f(x);
}

int32_t apply_alias(Handler f, int32_t x) {  // BANNED
  return f(x);
}

int32_t apply_member(int32_t (Widget::*f)(int32_t), Widget& w, int32_t x) {  // BANNED
  return (w.*f)(x);
}

int32_t count_pointers(const std::vector<int32_t (*)(int32_t)>& items) {  // BANNED
  return items.empty() ? 0 : 1;
}

int32_t apply_boxed(std::function<int32_t(int32_t)> f, int32_t x) {  // BANNED
  return f(x);
}

int32_t apply_boxed_ref(const std::function<int32_t(int32_t)>& f, int32_t x) {  // BANNED
  return f(x);
}

int32_t apply_boxed_ptr(const std::function<int32_t(int32_t)>* f, int32_t x) {  // BANNED
  return (*f)(x);
}

int32_t count_boxed(const std::vector<std::function<int32_t(int32_t)>>& items) {  // BANNED
  return items.empty() ? 0 : 1;
}

//@ requires x < 0x7FFFFFFF
int32_t next(int32_t& x);

int32_t through_reference(int32_t& x) {
  int32_t (&fr)(int32_t&) = next;  // BANNED also: lvalue_references
  return fr(x);
}

int32_t total = 0;

// A std::function holds its target behind a pointer. What the target changes counts where the function is made, decision 0037.
//@ requires total < 0x7FFFFFFF
//@ modifies total
void boxed_write() {
  std::function<void()> f = [] { total += 1; };  // BANNED also: lambdas
  f();
}

// The same with no modifies line. The write hides behind the pointer, and the gate still sees it.
void boxed_write_unlisted() {
  std::function<void()> f = [] { total += 1; };  // BANNED also: lambdas, global_state
  f();
}
