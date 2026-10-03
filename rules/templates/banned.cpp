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

template <> int twice<int>(int x) { return x * 2; }  // BANNED

template <int N>  // BANNED
struct Fixed {
  int data = N;
};

template <template <typename> class C>  // BANNED
struct Wrap {
  C<int>* inner = nullptr;
};

template <typename T>
constexpr int kSize = 1;

template <> constexpr int kSize<bool> = 2;  // BANNED

template <typename T>
constexpr int kPtr = 1;

template <typename T> constexpr int kPtr<T*> = 2;  // BANNED
