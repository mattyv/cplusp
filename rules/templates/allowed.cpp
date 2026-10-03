template <typename T>
T twice(T x) {
  return x + x;
}

template <typename T>
struct Box {
  T value;
};

int use() {
  Box<int> b{twice(2)};
  return b.value;
}
