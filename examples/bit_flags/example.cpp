#include <cstdint>

// A set of flags in an enum class. The enumerators are powers of two, and a value of the type is any bit pattern of uint32_t, because the
// underlying type is fixed. So Read | Write is a legal value that no enumerator names. The enum_cast rule asks that a cast from an integer
// is an enumerator, and a flags type cannot meet it. The model is a bv32 for that reason, and a datatype of enumerators or a set of them
// would have no value for Read | Write, nor for a bit that no enumerator names. The operators are free functions with by-value
// parameters, and they have no precondition: every pattern is a value. Each contract states the result on the bits. has(flags, flag)
// says that every bit of flag is set in flags, which is the usual test for one flag.
enum class Flag : uint32_t { None = 0, Read = 1, Write = 2, Exec = 4, Admin = 8 };

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

// A verified caller. Granting a flag sets it, and the flags it had stay set.
//@ ensures has(result, flag) && (has(flags, Flag::Read) ==> has(result, Flag::Read))
Flag grant(Flag flags, Flag flag) {
  return flags | flag;
}

// The flags both sides share are the flags in the overlap.
//@ ensures result == (has(a, Flag::Write) && has(b, Flag::Write))
bool both_may_write(Flag a, Flag b) {
  return has(a & b, Flag::Write);
}

//@ ensures result == true
bool reader_and_writer_cannot_exec() {
  Flag f = Flag::Read | Flag::Write;
  return has(f, Flag::Write) && !has(f, Flag::Exec);
}
