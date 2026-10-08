#include <cstdint>

// A member function is refused as a member, whatever its name, decision 0069. Its name never reaches the Dafny text.
struct D {
  ~D() {}
  int32_t operator()(int32_t x) const { return x; }
};
