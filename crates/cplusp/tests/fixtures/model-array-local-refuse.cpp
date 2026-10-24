#include <array>
#include <cstdint>

// A brace list of another count, and a local array from another array, decision 0184.
//@ ensures true
int32_t short_list() {
  const std::array<int32_t, 3> t = {1, 2};
  return t[0];
}

//@ ensures true
int32_t copied(const std::array<int32_t, 2>& a) {
  const std::array<int32_t, 2> t = a;
  return t[0];
}

struct D {
  int32_t a;
  //@ ensures true
  ~D() {}
};

//@ ensures true
int32_t with_destructor() {
  const std::array<D, 1> t = {D{1}};
  return t[0].a;
}
