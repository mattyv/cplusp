#include <cstdint>
#include <vector>

// A struct that holds a sequence is a parameter only, decision 0076.
struct Node {
  std::vector<uint8_t> prefix;
  std::vector<Node> children;
};

struct Wrapper {
  Node n;
};

uint8_t local(const Node& n) {
  Node c = n.children[0];
  return 0;
}

Node result(const Node& n) {
  return n.children[0];
}

uint8_t nested(const Wrapper& w) {
  Wrapper c = w;
  return 0;
}
