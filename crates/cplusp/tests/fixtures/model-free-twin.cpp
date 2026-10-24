#include <cstdint>

// A free function with one return and no call has a function twin, and a contract calls it by its name, decision 0176.
enum class Flag : uint32_t { None = 0, Read = 1, Write = 2, Exec = 4 };

//@ ensures result == ((static_cast<uint32_t>(flags) & static_cast<uint32_t>(flag)) == static_cast<uint32_t>(flag))
bool has(Flag flags, Flag flag) {
  return (static_cast<uint32_t>(flags) & static_cast<uint32_t>(flag)) == static_cast<uint32_t>(flag);
}

//@ ensures static_cast<uint32_t>(result) == (static_cast<uint32_t>(a) | static_cast<uint32_t>(b))
//@ ensures has(result, a) && has(result, b)
Flag operator|(Flag a, Flag b) {
  return static_cast<Flag>(static_cast<uint32_t>(a) | static_cast<uint32_t>(b));
}

//@ ensures static_cast<uint32_t>(result) == (static_cast<uint32_t>(a) & static_cast<uint32_t>(b))
//@ ensures has(a, result) && has(b, result)
Flag operator&(Flag a, Flag b) {
  return static_cast<Flag>(static_cast<uint32_t>(a) & static_cast<uint32_t>(b));
}

//@ ensures has(result, flag) && (has(flags, Flag::Read) ==> has(result, Flag::Read))
Flag grant(Flag flags, Flag flag) {
  return flags | flag;
}

//@ ensures result == (has(a, Flag::Write) && has(b, Flag::Write))
bool both_may_write(Flag a, Flag b) {
  return has(a & b, Flag::Write);
}

// A twin with a plain integer, and a caller that proves through it.
//@ requires -1000 <= x && x <= 1000
//@ ensures result == 2 * x
int32_t twice(int32_t x) {
  return 2 * x;
}

//@ ensures result == twice(3)
int32_t six() {
  return 6;
}
