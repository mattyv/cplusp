#include <cstdint>
template <typename T>
struct Box {
  T value;
};

template <> struct Box<bool> { bool value = false; };  // BANNED

template <typename T>
struct Holder {
  T value;
};

template <typename T> struct Holder<T*> { int32_t tag = 1; };  // BANNED

template <typename T>
T twice(T x) {
  return x + x;
}

template <> int32_t twice<int32_t>(int32_t x) { return x * 2; }  // BANNED

template <int32_t N>  // BANNED
struct Fixed {
  int32_t data = N;
};

#include <type_traits>

enum class Width { Narrow, Wide };

// An enum template argument is a value the compiler substitutes. The cast it writes for that is no cast in the source, so the
// alias line below carries no finding of its own. The trial on a real file found it reported as a C-style cast.
template <Width width>  // BANNED
struct Sized {
  using Count = std::conditional_t<width == Width::Narrow, int32_t, int64_t>;
  Count n = 0;
};

int64_t wide_count() {
  Sized<Width::Wide> s;
  return s.n;
}

template <template <typename> class C>  // BANNED
struct Wrap {
  C<int32_t> inner{};
};

template <typename T>
constexpr int32_t kSize = 1;

template <> constexpr int32_t kSize<bool> = 2;  // BANNED

template <typename T>
constexpr int32_t kPtr = 1;

template <typename T> constexpr int32_t kPtr<T*> = 2;  // BANNED
