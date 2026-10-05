#include <array>
#include <cstddef>
#include <cstdint>

// A table indexed by an enum class. The enumerators carry their values, 0, 1 and 2, and static_cast<size_t>(level) is the index. The
// contract holds the bound: a subscript on a std::array of three needs an index below 3. In verified code a Level is always an
// enumerator, because the enum_cast rule asks a cast from an integer to carry a precondition that the integer is one, as lookup_code
// does. So the bound holds for every caller, and the prover proves it from the enumerators. The C++ language allows other values of a
// Level, and that is why the bound is written in the contract and is not left to the type.
enum class Level : uint8_t { Low = 0, Medium = 1, High = 2 };

//@ requires static_cast<size_t>(level) < 3
//@ ensures result == table[static_cast<size_t>(level)]
int32_t lookup(const std::array<int32_t, 3>& table, Level level) {
  return table[static_cast<size_t>(level)];
}

// The table is built by value and read through the same function.
//@ ensures result[0] == 10 && result[1] == 20 && result[2] == 30
std::array<int32_t, 3> default_table() {
  return {10, 20, 30};
}

//@ ensures result == 30
int32_t high_weight() {
  return lookup(default_table(), Level::High);
}

// A cast from an integer: the contract says the integer is an enumerator, and the caller proves it.
//@ requires code < 3
//@ ensures result == table[code]
int32_t lookup_code(const std::array<int32_t, 3>& table, uint8_t code) {
  return lookup(table, static_cast<Level>(code));
}
