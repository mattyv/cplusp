#include <cstdint>

// A member function template, and an instance whose body has no rule, decision 0180.
struct Meter {
  int32_t v_;

  //@ ensures result == v_
  template <typename T>
  T as() const {
    return v_;
  }
};

//@ ensures result == 4
template <typename T>
int32_t width(T a) {
  return sizeof(a);
}

//@ ensures result == 4
int32_t width32(int32_t a) {
  return width(a);
}

// A template that the file never uses has no instance, so nothing proves its contract.
//@ ensures result == a + 1
template <typename T>
T unused(T a) {
  return a;
}

// An instance that the file only declares has no body here.
//@ ensures result >= a && result >= b
template <typename T>
T larger(T a, T b) {
  return a < b ? b : a;
}

extern template int32_t larger<int32_t>(int32_t, int32_t);

//@ ensures result >= a && result >= b
int32_t larger32(int32_t a, int32_t b) {
  return larger(a, b);
}

// A type argument that has no type of the model.
template <typename T>
struct Box {
  T v;
};

//@ ensures result.v == a.v
template <typename T>
T keep(T a) {
  return a;
}

Box<int32_t> keep_box(Box<int32_t> a) {
  return keep(a);
}

// A specialization that overload resolution makes and drops is no instance.
//@ ensures result == a + 1
template <typename T>
T near(T a) {
  return a;
}

//@ ensures result == a
int32_t near(int32_t a) {
  return a;
}

//@ ensures result == a
int32_t near_of(int32_t a) {
  return near(a);
}

// A type argument that has no Dafny name yet.
#include <vector>

//@ ensures result == v.size()
template <typename T>
uint64_t count(const T& v) {
  return v.size();
}

//@ ensures result == v.size()
uint64_t count32(const std::vector<int32_t>& v) {
  return count(v);
}
