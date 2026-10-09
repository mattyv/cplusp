#include <cstdint>

// A case that falls into the next one where the source marks it, a default, a break in another place, an enum with values
// written, a cast of an enum, and an order of enums, are refused at their lines, decision 0109. The gate refuses a switch that
// misses an enumerator, and a fall with no mark.
enum class Kind : uint8_t { Small, Medium, Large };
enum class Flag : uint32_t { Read = 1, Write = 2 };

int32_t marked(Kind k) {
  int32_t n = 0;
  switch (k) {
    case Kind::Small:
      n = 1;
      [[fallthrough]];
    case Kind::Medium:
      return 2;
    case Kind::Large:
      return 3;
  }
  return n;
}

int32_t with_default(Kind k) {
  switch (k) {
    case Kind::Small:
      return 1;
    default:
      return 2;
  }
}

int32_t early(Kind k, bool b) {
  switch (k) {
    case Kind::Small:
      if (b) {
        break;
      }
      return 1;
    case Kind::Medium:
      return 2;
    case Kind::Large:
      return 3;
  }
  return 0;
}

bool readable(Flag f) {
  return f == Flag::Read;
}

uint8_t code(Kind k) {
  return static_cast<uint8_t>(k);
}

bool smaller(Kind a, Kind b) {
  return a < b;
}

// An order of enums in a contract, decisions 0114 and 0115. Dafny would read `<` as an order of rank it does not know.
//@ ensures k < Kind::Large ==> result
bool below(Kind k) {
  return k == Kind::Small;
}

// Two enums with one plain name: a contract cannot name an enumerator of either yet, decision 0114.
namespace na {
enum class Mode : uint8_t { Off, On };
}
namespace nb {
enum class Mode : uint8_t { On, Off };
}

//@ ensures result == Mode::On
na::Mode on() {
  return na::Mode::On;
}

// An enumerator whose name Dafny cannot read is refused at the line of its enum, decision 0109.
enum class Odd : uint8_t { P$, Q };

bool is_q(Odd o) {
  return o == Odd::Q;
}

// A struct with a field of that enum is dropped with it, and adds no refusal of its own, decision 0114.
struct OddBox {
  Odd o;
  int32_t n;
};

int32_t box_n(OddBox b) {
  return b.n;
}
