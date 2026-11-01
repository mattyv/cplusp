#include <cstdint>
namespace a {
struct T {
  static int32_t up();
};
//@ ensures result == T::up()
int32_t f() { return 7; }
}
namespace b {
struct T {
  //@ ensures result == 7
  static int32_t up() { return 7; }
};
}
