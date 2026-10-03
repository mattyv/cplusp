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

template <typename T> struct Holder<T*> { T* value = nullptr; };  // BANNED

template <typename T>
T twice(T x) {
  return x + x;
}

template <> int32_t twice<int32_t>(int32_t x) { return x * 2; }  // BANNED

template <int32_t N>  // BANNED
struct Fixed {
  int32_t data = N;
};

template <template <typename> class C>  // BANNED
struct Wrap {
  C<int32_t>* inner = nullptr;
};

template <typename T>
constexpr int32_t kSize = 1;

template <> constexpr int32_t kSize<bool> = 2;  // BANNED

template <typename T>
constexpr int32_t kPtr = 1;

template <typename T> constexpr int32_t kPtr<T*> = 2;  // BANNED
