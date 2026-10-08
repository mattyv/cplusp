#include <cstdint>

// The check of impure operators reads types, so it judges each instantiation, decision 0055.
// In Wrap<int32_t*> the parameter is a pointer to non-const, so the operator can write.
template <class T>
struct Wrap {
  T v{};
  bool operator==(T other) const {
    return v == other;
  }
};

bool same(const Wrap<int32_t*>& w, int32_t* p) {
  return w == p;
}

// A forwarding reference that becomes a const reference in every instantiation cannot write.
struct Box {
  int32_t v = 0;
};

template <class T>
bool operator!=(const Box& a, T&& b) {
  return a.v != b.v;
}

bool differ(const Box& a, const Box& b) {
  return a != b;
}

// An operator in a template that nothing instantiates is judged by its spelling, as before decision 0055.
template <class T>
struct Unused {
  T v{};
  Unused& operator+=(const Unused& o) {
    v += o.v;
    return *this;
  }
  bool operator==(const Unused& o) {
    return v == o.v;
  }
};
