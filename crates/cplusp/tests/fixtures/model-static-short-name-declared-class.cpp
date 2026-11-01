#include <cstdint>
struct T {
  //@ ensures result == 7
  static int32_t up() { return 7; }
};
namespace a {
struct T;
//@ ensures result == T::up()
int32_t f() { return 7; }
}
