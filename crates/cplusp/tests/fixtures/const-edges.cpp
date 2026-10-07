#include <cstdint>
#include <memory>
#include <optional>
#include <random>

namespace std {
struct deque {
  int32_t n = 0;
  int32_t& at(int32_t) {
    n += 1;
    return n;
  }
};
}  // namespace std

int32_t first(const std::unique_ptr<std::deque>& p) {
  return p->at(0) + 1;
}

struct Opaque;

//@ ensures true
void take_opaque(const Opaque& o);

void hand_over(const std::unique_ptr<Opaque>& p) {
  take_opaque(*p);
}

// A mutable field stays writable through a const reference.
struct Mut {
  mutable int32_t x = 0;
};

void take_mut(const Mut& m) {
  m.x = 1;
}

void through_mutable(const std::unique_ptr<Mut>& p) {
  take_mut(*p);
}

// A constructor of the library may call a method of the file on its argument. The engine calls generate, which writes.
struct Seq {
  using result_type = std::uint32_t;
  int32_t calls = 0;
  template <class It>
  void generate(It first, It last) {
    calls += 1;
    for (; first != last; ++first) {
      *first = 1;
    }
  }
};

void seeded(const std::unique_ptr<Seq>& p) {
  std::mt19937 gen(*p);
}

// A cast of a pointer to an integer is a cast, and no read.
void as_number(const std::unique_ptr<int32_t>& p) {
  std::uintptr_t a = reinterpret_cast<std::uintptr_t>(p.get());
  *reinterpret_cast<int32_t*>(a) = 1;
}

// A library constructor copies a type of the file through that type's own constructor, which may write, decision 0045.
struct Counter {
  int32_t n = 0;
  Counter() = default;
  Counter(Counter& o) : n(o.n) {
    o.n += 1;
  }
  Counter(const Counter& o) : n(o.n) {}
};

int32_t snapshot(const std::unique_ptr<Counter>& p) {
  std::optional<Counter> copy(*p);
  return copy->n;
}
