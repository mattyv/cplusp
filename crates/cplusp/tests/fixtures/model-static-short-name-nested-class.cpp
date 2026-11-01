#include <cstdint>
struct Outer {
  struct T {
    //@ ensures result == 7
    static int32_t up() { return 7; }
  };
  //@ ensures result == T::up()
  int32_t get() const { return 7; }
  int32_t v;
};
//@ ensures result == 7
int32_t f(const Outer& o) { return o.get(); }
