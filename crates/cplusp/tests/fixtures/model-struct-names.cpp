#include <cstdint>
#include <vector>

// A struct or a field whose name Dafny cannot read is refused at the struct's line, decision 0069.
struct Node {
  std::vector<Node> ch;
  int32_t a$b;
};

struct N$ {
  int32_t x;
};

int32_t f(const Node& n) {
  return 0;
}

int32_t g(const N$& m) {
  return m.x;
}
