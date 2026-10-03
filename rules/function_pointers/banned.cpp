#include <functional>
#include <vector>

struct Widget {
  int size(int scale);
};

using Handler = int (*)(int);  // BANNED

int apply(int (*f)(int), int x) {  // BANNED
  return f(x);
}

int apply_alias(Handler f, int x) {  // BANNED
  return f(x);
}

int apply_member(int (Widget::*f)(int), Widget& w, int x) {  // BANNED
  return (w.*f)(x);
}

int count_pointers(const std::vector<int (*)(int)>& items) {  // BANNED
  return items.empty() ? 0 : 1;
}

int apply_boxed(std::function<int(int)> f, int x) {  // BANNED
  return f(x);
}

int apply_boxed_ref(const std::function<int(int)>& f, int x) {  // BANNED
  return f(x);
}

int apply_boxed_ptr(const std::function<int(int)>* f, int x) {  // BANNED
  return (*f)(x);
}

int count_boxed(const std::vector<std::function<int(int)>>& items) {  // BANNED
  return items.empty() ? 0 : 1;
}
