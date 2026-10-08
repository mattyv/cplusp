#include <cstdint>
#include <vector>

// Each failed obligation on a struct that holds a sequence is named at its line, decision 0076.
struct Node {
  std::vector<uint8_t> prefix;
  std::vector<Node> children;
};

uint8_t nested(const Node& n) {
  return n.children[0].prefix[0];
}

//@ decreases n
uint8_t forever(const Node& n) {
  return forever(n);
}
