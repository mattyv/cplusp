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
