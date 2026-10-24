#include <cstdint>

// A destructor and an operator() have models, decisions 0069 and 0178. Their names reach the Dafny text as words.
struct D {
  ~D() {}
  int32_t operator()(int32_t x) const { return x; }
};
