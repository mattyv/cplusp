#include <cstdint>
namespace a {
struct T {
  //@ ensures result == 3
  static int32_t up() { return 3; }
};
}
namespace b {
struct T {
  //@ ensures result == 7
  static int32_t up() { return 7; }
};
}
//@ ensures result == T::up()
int32_t f() { return 7; }
