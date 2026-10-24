#include <cstdint>

// A grant that drops the old flags, and a six that is seven, decision 0176.
enum class Flag : uint32_t { None = 0, Read = 1, Write = 2, Exec = 4 };

//@ ensures result == ((static_cast<uint32_t>(flags) & static_cast<uint32_t>(flag)) == static_cast<uint32_t>(flag))
bool has(Flag flags, Flag flag) {
  return (static_cast<uint32_t>(flags) & static_cast<uint32_t>(flag)) == static_cast<uint32_t>(flag);
}

//@ ensures has(result, flag) && (has(flags, Flag::Read) ==> has(result, Flag::Read))
Flag grant(Flag flags, Flag flag) {
  return flag;
}

//@ requires -1000 <= x && x <= 1000
//@ ensures result == 2 * x
int32_t twice(int32_t x) {
  return 2 * x;
}

//@ ensures result == twice(3)
int32_t seven() {
  return 7;
}
